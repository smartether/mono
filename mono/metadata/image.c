/*
 * image.c: Routines for manipulating an image stored in an
 * extended PE/COFF file.
 * 
 * Authors:
 *   Miguel de Icaza (miguel@ximian.com)
 *   Paolo Molaro (lupus@ximian.com)
 *
 * Copyright 2001-2003 Ximian, Inc (http://www.ximian.com)
 * Copyright 2004-2009 Novell, Inc (http://www.novell.com)
 *
 */

#include "../../unity/unity_utils.h"
#include "../../log.h"
#include <config.h>
#include <stdio.h>
#include <glib.h>
#include <errno.h>
#include <time.h>
#include <string.h>
#include "image.h"
#include "cil-coff.h"
#include "mono-endian.h"
#include "tabledefs.h"
#include "tokentype.h"
#include "metadata-internals.h"
#include "profiler-private.h"
#include "loader.h"
#include "marshal.h"
#include "coree.h"
#include <mono/io-layer/io-layer.h>
#include <mono/utils/mono-logger.h>
#include <mono/utils/mono-path.h>
#include <mono/utils/mono-mmap.h>
#include <mono/utils/mono-io-portability.h>
#include <mono/metadata/class-internals.h>
#include <mono/metadata/assembly.h>
#include <mono/metadata/object-internals.h>
#include <mono/metadata/security-core-clr.h>
#include <mono/metadata/verify-internals.h>
#include <sys/types.h>
#include <sys/stat.h>
#ifdef HAVE_UNISTD_H
#include <unistd.h>
#endif

#define INVALID_ADDRESS 0xffffffff

/********** JNI Interface   ************/
/*
static JNIEnv* gEnv;
static char* gPkgNameC;
static char* gFilesDir;


void mono_image_Java_JNI_Pkg_Set(JNIEnv* env, jobject x, jstring pkgName){
        LOGD("$$ set package name as %s", pkgName);
        gEnv = env;
        jboolean isCopy = 0;
        gPkgNameC = (*env)->GetStringUTFChars(env, pkgName, &isCopy);
}

void mono_image_Java_JNI_Pkg_SetFilesDir(JNIEnv* env, jobject x, jstring filesDir){
        LOGD("$$ set fileDir as %s", filesDir);
        jboolean isCopy = 0;
        gFilesDir = (*env)->GetStringUTFChars(env, filesDir, &isCopy);
}
*/

/*
 * Keeps track of the various assemblies loaded
 */
static GHashTable *loaded_images_hash;
static GHashTable *loaded_images_refonly_hash;

static gboolean debug_assembly_unload = FALSE;

#define mono_images_lock() if (mutex_inited) EnterCriticalSection (&images_mutex)
#define mono_images_unlock() if (mutex_inited) LeaveCriticalSection (&images_mutex)
static gboolean mutex_inited;
static CRITICAL_SECTION images_mutex;

/* returns offset relative to image->raw_data */
guint32
mono_cli_rva_image_map (MonoImage *image, guint32 addr)
{
	MonoCLIImageInfo *iinfo = image->image_info;
	const int top = iinfo->cli_section_count;
	MonoSectionTable *tables = iinfo->cli_section_tables;
	int i;
	
	for (i = 0; i < top; i++){
		if ((addr >= tables->st_virtual_address) &&
		    (addr < tables->st_virtual_address + tables->st_raw_data_size)){
#ifdef USE_COREE
			if (image->is_module_handle)
				return addr;
#endif
			return addr - tables->st_virtual_address + tables->st_raw_data_ptr;
		}
		tables++;
	}
	return INVALID_ADDRESS;
}

/**
 * mono_images_rva_map:
 * @image: a MonoImage
 * @addr: relative virtual address (RVA)
 *
 * This is a low-level routine used by the runtime to map relative
 * virtual address (RVA) into their location in memory. 
 *
 * Returns: the address in memory for the given RVA, or NULL if the
 * RVA is not valid for this image. 
 */
char *
mono_image_rva_map (MonoImage *image, guint32 addr)
{
	MonoCLIImageInfo *iinfo = image->image_info;
	const int top = iinfo->cli_section_count;
	MonoSectionTable *tables = iinfo->cli_section_tables;
	int i;
	
	for (i = 0; i < top; i++){
		if ((addr >= tables->st_virtual_address) &&
		    (addr < tables->st_virtual_address + tables->st_raw_data_size)){
			if (!iinfo->cli_sections [i]) {
				if (!mono_image_ensure_section_idx (image, i))
					return NULL;
			}
#ifdef USE_COREE
			if (image->is_module_handle)
				return image->raw_data + addr;
#endif
			return (char*)iinfo->cli_sections [i] +
				(addr - tables->st_virtual_address);
		}
		tables++;
	}
	return NULL;
}

/**
 * mono_images_init:
 *
 *  Initialize the global variables used by this module.
 */
void
mono_images_init (void)
{
	InitializeCriticalSection (&images_mutex);

	loaded_images_hash = g_hash_table_new (g_str_hash, g_str_equal);
	loaded_images_refonly_hash = g_hash_table_new (g_str_hash, g_str_equal);

	debug_assembly_unload = g_getenv ("MONO_DEBUG_ASSEMBLY_UNLOAD") != NULL;

	mutex_inited = TRUE;
}

/**
 * mono_images_cleanup:
 *
 *  Free all resources used by this module.
 */
void
mono_images_cleanup (void)
{
	DeleteCriticalSection (&images_mutex);

	g_hash_table_destroy (loaded_images_hash);
	g_hash_table_destroy (loaded_images_refonly_hash);

	mutex_inited = FALSE;
}

/**
 * mono_image_ensure_section_idx:
 * @image: The image we are operating on
 * @section: section number that we will load/map into memory
 *
 * This routine makes sure that we have an in-memory copy of
 * an image section (.text, .rsrc, .data).
 *
 * Returns: TRUE on success
 */
int
mono_image_ensure_section_idx (MonoImage *image, int section)
{
	MonoCLIImageInfo *iinfo = image->image_info;
	MonoSectionTable *sect;
	gboolean writable;
	
	g_return_val_if_fail (section < iinfo->cli_section_count, FALSE);

	if (iinfo->cli_sections [section] != NULL)
		return TRUE;

	sect = &iinfo->cli_section_tables [section];
	
	writable = sect->st_flags & SECT_FLAGS_MEM_WRITE;

	if (sect->st_raw_data_ptr + sect->st_raw_data_size > image->raw_data_len)
		return FALSE;
#ifdef USE_COREE
	if (image->is_module_handle)
		iinfo->cli_sections [section] = image->raw_data + sect->st_virtual_address;
	else
#endif
	/* FIXME: we ignore the writable flag since we don't patch the binary */
	iinfo->cli_sections [section] = image->raw_data + sect->st_raw_data_ptr;
	return TRUE;
}

/**
 * mono_image_ensure_section:
 * @image: The image we are operating on
 * @section: section name that we will load/map into memory
 *
 * This routine makes sure that we have an in-memory copy of
 * an image section (.text, .rsrc, .data).
 *
 * Returns: TRUE on success
 */
int
mono_image_ensure_section (MonoImage *image, const char *section)
{
	MonoCLIImageInfo *ii = image->image_info;
	int i;
	
	for (i = 0; i < ii->cli_section_count; i++){
		if (strncmp (ii->cli_section_tables [i].st_name, section, 8) != 0)
			continue;
		
		return mono_image_ensure_section_idx (image, i);
	}
	return FALSE;
}

static int
load_section_tables (MonoImage *image, MonoCLIImageInfo *iinfo, guint32 offset)
{
	const int top = iinfo->cli_header.coff.coff_sections;
	int i;

	iinfo->cli_section_count = top;
	iinfo->cli_section_tables = g_new0 (MonoSectionTable, top);
	iinfo->cli_sections = g_new0 (void *, top);
	
	for (i = 0; i < top; i++){
		MonoSectionTable *t = &iinfo->cli_section_tables [i];

		if (offset + sizeof (MonoSectionTable) > image->raw_data_len)
			return FALSE;
		memcpy (t, image->raw_data + offset, sizeof (MonoSectionTable));
		offset += sizeof (MonoSectionTable);

#if G_BYTE_ORDER != G_LITTLE_ENDIAN
		t->st_virtual_size = GUINT32_FROM_LE (t->st_virtual_size);
		t->st_virtual_address = GUINT32_FROM_LE (t->st_virtual_address);
		t->st_raw_data_size = GUINT32_FROM_LE (t->st_raw_data_size);
		t->st_raw_data_ptr = GUINT32_FROM_LE (t->st_raw_data_ptr);
		t->st_reloc_ptr = GUINT32_FROM_LE (t->st_reloc_ptr);
		t->st_lineno_ptr = GUINT32_FROM_LE (t->st_lineno_ptr);
		t->st_reloc_count = GUINT16_FROM_LE (t->st_reloc_count);
		t->st_line_count = GUINT16_FROM_LE (t->st_line_count);
		t->st_flags = GUINT32_FROM_LE (t->st_flags);
#endif
		/* consistency checks here */
	}

	return TRUE;
}

static gboolean
load_cli_header (MonoImage *image, MonoCLIImageInfo *iinfo)
{
	guint32 offset;
	
	offset = mono_cli_rva_image_map (image, iinfo->cli_header.datadir.pe_cli_header.rva);
	if (offset == INVALID_ADDRESS)
		return FALSE;

	if (offset + sizeof (MonoCLIHeader) > image->raw_data_len)
		return FALSE;
	memcpy (&iinfo->cli_cli_header, image->raw_data + offset, sizeof (MonoCLIHeader));

#if G_BYTE_ORDER != G_LITTLE_ENDIAN
#define SWAP32(x) (x) = GUINT32_FROM_LE ((x))
#define SWAP16(x) (x) = GUINT16_FROM_LE ((x))
#define SWAPPDE(x) do { (x).rva = GUINT32_FROM_LE ((x).rva); (x).size = GUINT32_FROM_LE ((x).size);} while (0)
	SWAP32 (iinfo->cli_cli_header.ch_size);
	SWAP32 (iinfo->cli_cli_header.ch_flags);
	SWAP32 (iinfo->cli_cli_header.ch_entry_point);
	SWAP16 (iinfo->cli_cli_header.ch_runtime_major);
	SWAP16 (iinfo->cli_cli_header.ch_runtime_minor);
	SWAPPDE (iinfo->cli_cli_header.ch_metadata);
	SWAPPDE (iinfo->cli_cli_header.ch_resources);
	SWAPPDE (iinfo->cli_cli_header.ch_strong_name);
	SWAPPDE (iinfo->cli_cli_header.ch_code_manager_table);
	SWAPPDE (iinfo->cli_cli_header.ch_vtable_fixups);
	SWAPPDE (iinfo->cli_cli_header.ch_export_address_table_jumps);
	SWAPPDE (iinfo->cli_cli_header.ch_eeinfo_table);
	SWAPPDE (iinfo->cli_cli_header.ch_helper_table);
	SWAPPDE (iinfo->cli_cli_header.ch_dynamic_info);
	SWAPPDE (iinfo->cli_cli_header.ch_delay_load_info);
	SWAPPDE (iinfo->cli_cli_header.ch_module_image);
	SWAPPDE (iinfo->cli_cli_header.ch_external_fixups);
	SWAPPDE (iinfo->cli_cli_header.ch_ridmap);
	SWAPPDE (iinfo->cli_cli_header.ch_debug_map);
	SWAPPDE (iinfo->cli_cli_header.ch_ip_map);
#undef SWAP32
#undef SWAP16
#undef SWAPPDE
#endif
	/* Catch new uses of the fields that are supposed to be zero */

	if ((iinfo->cli_cli_header.ch_eeinfo_table.rva != 0) ||
	    (iinfo->cli_cli_header.ch_helper_table.rva != 0) ||
	    (iinfo->cli_cli_header.ch_dynamic_info.rva != 0) ||
	    (iinfo->cli_cli_header.ch_delay_load_info.rva != 0) ||
	    (iinfo->cli_cli_header.ch_module_image.rva != 0) ||
	    (iinfo->cli_cli_header.ch_external_fixups.rva != 0) ||
	    (iinfo->cli_cli_header.ch_ridmap.rva != 0) ||
	    (iinfo->cli_cli_header.ch_debug_map.rva != 0) ||
	    (iinfo->cli_cli_header.ch_ip_map.rva != 0)){

		/*
		 * No need to scare people who are testing this, I am just
		 * labelling this as a LAMESPEC
		 */
		/* g_warning ("Some fields in the CLI header which should have been zero are not zero"); */

	}
	    
	return TRUE;
}

static gboolean
load_metadata_ptrs (MonoImage *image, MonoCLIImageInfo *iinfo)
{
	guint32 offset, size;
	guint16 streams;
	int i;
	guint32 pad;
	char *ptr;
	
	offset = mono_cli_rva_image_map (image, iinfo->cli_cli_header.ch_metadata.rva);
	if (offset == INVALID_ADDRESS)
		return FALSE;

	size = iinfo->cli_cli_header.ch_metadata.size;

	if (offset + size > image->raw_data_len)
		return FALSE;
	image->raw_metadata = image->raw_data + offset;

	/* 24.2.1: Metadata root starts here */
	ptr = image->raw_metadata;

	if (strncmp (ptr, "BSJB", 4) == 0){
		guint32 version_string_len;

		ptr += 4;
		image->md_version_major = read16 (ptr);
		ptr += 2;
		image->md_version_minor = read16 (ptr);
		ptr += 6;

		version_string_len = read32 (ptr);
		ptr += 4;
		image->version = g_strndup (ptr, version_string_len);
		ptr += version_string_len;
		pad = ptr - image->raw_metadata;
		if (pad % 4)
			ptr += 4 - (pad % 4);
	} else
		return FALSE;

	/* skip over flags */
	ptr += 2;
	
	streams = read16 (ptr);
	ptr += 2;

	for (i = 0; i < streams; i++){
		if (strncmp (ptr + 8, "#~", 3) == 0){
			image->heap_tables.data = image->raw_metadata + read32 (ptr);
			image->heap_tables.size = read32 (ptr + 4);
			ptr += 8 + 3;
		} else if (strncmp (ptr + 8, "#Strings", 9) == 0){
			image->heap_strings.data = image->raw_metadata + read32 (ptr);
			image->heap_strings.size = read32 (ptr + 4);
			ptr += 8 + 9;
		} else if (strncmp (ptr + 8, "#US", 4) == 0){
			image->heap_us.data = image->raw_metadata + read32 (ptr);
			image->heap_us.size = read32 (ptr + 4);
			ptr += 8 + 4;
		} else if (strncmp (ptr + 8, "#Blob", 6) == 0){
			image->heap_blob.data = image->raw_metadata + read32 (ptr);
			image->heap_blob.size = read32 (ptr + 4);
			ptr += 8 + 6;
		} else if (strncmp (ptr + 8, "#GUID", 6) == 0){
			image->heap_guid.data = image->raw_metadata + read32 (ptr);
			image->heap_guid.size = read32 (ptr + 4);
			ptr += 8 + 6;
		} else if (strncmp (ptr + 8, "#-", 3) == 0) {
			image->heap_tables.data = image->raw_metadata + read32 (ptr);
			image->heap_tables.size = read32 (ptr + 4);
			ptr += 8 + 3;
			image->uncompressed_metadata = TRUE;
			mono_trace (G_LOG_LEVEL_INFO, MONO_TRACE_ASSEMBLY, "Assembly '%s' has the non-standard metadata heap #-.\nRecompile it correctly (without the /incremental switch or in Release mode).\n", image->name);
		} else {
			g_message ("Unknown heap type: %s\n", ptr + 8);
			ptr += 8 + strlen (ptr + 8) + 1;
		}
		pad = ptr - image->raw_metadata;
		if (pad % 4)
			ptr += 4 - (pad % 4);
	}

	g_assert (image->heap_guid.data);
	g_assert (image->heap_guid.size >= 16);

	image->guid = mono_guid_to_string ((guint8*)image->heap_guid.data);

	return TRUE;
}

/*
 * Load representation of logical metadata tables, from the "#~" stream
 */
static gboolean
load_tables (MonoImage *image)
{
	const char *heap_tables = image->heap_tables.data;
	const guint32 *rows;
	guint64 valid_mask, sorted_mask;
	int valid = 0, table;
	int heap_sizes;
	
	heap_sizes = heap_tables [6];
	image->idx_string_wide = ((heap_sizes & 0x01) == 1);
	image->idx_guid_wide   = ((heap_sizes & 0x02) == 2);
	image->idx_blob_wide   = ((heap_sizes & 0x04) == 4);
	
	valid_mask = read64 (heap_tables + 8);
	sorted_mask = read64 (heap_tables + 16);
	rows = (const guint32 *) (heap_tables + 24);
	
	for (table = 0; table < 64; table++){
		if ((valid_mask & ((guint64) 1 << table)) == 0){
			if (table > MONO_TABLE_LAST)
				continue;
			image->tables [table].rows = 0;
			continue;
		}
		if (table > MONO_TABLE_LAST) {
			g_warning("bits in valid must be zero above 0x2d (II - 23.1.6)");
		} else {
			image->tables [table].rows = read32 (rows);
		}
		/*if ((sorted_mask & ((guint64) 1 << table)) == 0){
			g_print ("table %s (0x%02x) is sorted\n", mono_meta_table_name (table), table);
		}*/
		rows++;
		valid++;
	}

	image->tables_base = (heap_tables + 24) + (4 * valid);

	/* They must be the same */
	g_assert ((const void *) image->tables_base == (const void *) rows);

	mono_metadata_compute_table_bases (image);
	return TRUE;
}

static gboolean
load_metadata (MonoImage *image, MonoCLIImageInfo *iinfo)
{
	if (!load_metadata_ptrs (image, iinfo))
		return FALSE;

	return load_tables (image);
}

void
mono_image_check_for_module_cctor (MonoImage *image)
{
	MonoTableInfo *t, *mt;
	t = &image->tables [MONO_TABLE_TYPEDEF];
	mt = &image->tables [MONO_TABLE_METHOD];
	if (mono_framework_version () == 1) {
		image->checked_module_cctor = TRUE;
		return;
	}
	if (image->dynamic) {
		/* FIXME: */
		image->checked_module_cctor = TRUE;
		return;
	}
	if (t->rows >= 1) {
		guint32 nameidx = mono_metadata_decode_row_col (t, 0, MONO_TYPEDEF_NAME);
		const char *name = mono_metadata_string_heap (image, nameidx);
		if (strcmp (name, "<Module>") == 0) {
			guint32 first_method = mono_metadata_decode_row_col (t, 0, MONO_TYPEDEF_METHOD_LIST) - 1;
			guint32 last_method;
			if (t->rows > 1)
				last_method = mono_metadata_decode_row_col (t, 1, MONO_TYPEDEF_METHOD_LIST) - 1;
			else 
				last_method = mt->rows;
			for (; first_method < last_method; first_method++) {
				nameidx = mono_metadata_decode_row_col (mt, first_method, MONO_METHOD_NAME);
				name = mono_metadata_string_heap (image, nameidx);
				if (strcmp (name, ".cctor") == 0) {
					image->has_module_cctor = TRUE;
					image->checked_module_cctor = TRUE;
					return;
				}
			}
		}
	}
	image->has_module_cctor = FALSE;
	image->checked_module_cctor = TRUE;
}

static void
load_modules (MonoImage *image)
{
	MonoTableInfo *t;

	if (image->modules)
		return;

	t = &image->tables [MONO_TABLE_MODULEREF];
	image->modules = g_new0 (MonoImage *, t->rows);
	image->modules_loaded = g_new0 (gboolean, t->rows);
	image->module_count = t->rows;
}

/**
 * mono_image_load_module:
 *
 *   Load the module with the one-based index IDX from IMAGE and return it. Return NULL if
 * it cannot be loaded.
 */
MonoImage*
mono_image_load_module (MonoImage *image, int idx)
{
	MonoTableInfo *t;
	MonoTableInfo *file_table;
	int i;
	char *base_dir;
	gboolean refonly = image->ref_only;
	GList *list_iter, *valid_modules = NULL;
	MonoImageOpenStatus status;

	if ((image->module_count == 0) || (idx > image->module_count))
		return NULL;
	if (image->modules_loaded [idx - 1])
		return image->modules [idx - 1];

	file_table = &image->tables [MONO_TABLE_FILE];
	for (i = 0; i < file_table->rows; i++) {
		guint32 cols [MONO_FILE_SIZE];
		mono_metadata_decode_row (file_table, i, cols, MONO_FILE_SIZE);
		if (cols [MONO_FILE_FLAGS] == FILE_CONTAINS_NO_METADATA)
			continue;
		valid_modules = g_list_prepend (valid_modules, (char*)mono_metadata_string_heap (image, cols [MONO_FILE_NAME]));
	}

	t = &image->tables [MONO_TABLE_MODULEREF];
	base_dir = g_path_get_dirname (image->name);

	{
		char *module_ref;
		const char *name;
		guint32 cols [MONO_MODULEREF_SIZE];
		/* if there is no file table, we try to load the module... */
		int valid = file_table->rows == 0;

		mono_metadata_decode_row (t, idx - 1, cols, MONO_MODULEREF_SIZE);
		name = mono_metadata_string_heap (image, cols [MONO_MODULEREF_NAME]);
		for (list_iter = valid_modules; list_iter; list_iter = list_iter->next) {
			/* be safe with string dups, but we could just compare string indexes  */
			if (strcmp (list_iter->data, name) == 0) {
				valid = TRUE;
				break;
			}
		}
		if (valid) {
			module_ref = g_build_filename (base_dir, name, NULL);
			image->modules [idx - 1] = mono_image_open_full (module_ref, &status, refonly);
			if (image->modules [idx - 1]) {
				mono_image_addref (image->modules [idx - 1]);
				image->modules [idx - 1]->assembly = image->assembly;
#ifdef USE_COREE
				if (image->modules [idx - 1]->is_module_handle)
					mono_image_fixup_vtable (image->modules [idx - 1]);
#endif
				/* g_print ("loaded module %s from %s (%p)\n", module_ref, image->name, image->assembly); */
			}
			g_free (module_ref);
		}
	}

	image->modules_loaded [idx - 1] = TRUE;

	g_free (base_dir);
	g_list_free (valid_modules);

	return image->modules [idx - 1];
}

static gpointer
class_key_extract (gpointer value)
{
	MonoClass *class = value;

	return GUINT_TO_POINTER (class->type_token);
}

static gpointer*
class_next_value (gpointer value)
{
	MonoClass *class = value;

	return (gpointer*)&class->next_class_cache;
}

void
mono_image_init (MonoImage *image)
{
	image->mempool = mono_mempool_new_size (512);
	mono_internal_hash_table_init (&image->class_cache,
				       g_direct_hash,
				       class_key_extract,
				       class_next_value);
	image->field_cache = g_hash_table_new (NULL, NULL);

	image->typespec_cache = g_hash_table_new (NULL, NULL);
	image->memberref_signatures = g_hash_table_new (NULL, NULL);
	image->helper_signatures = g_hash_table_new (g_str_hash, g_str_equal);
	image->method_signatures = g_hash_table_new (NULL, NULL);

	image->property_hash = mono_property_hash_new ();
	InitializeCriticalSection (&image->lock);
	InitializeCriticalSection (&image->szarray_cache_lock);
}

#if G_BYTE_ORDER != G_LITTLE_ENDIAN
#define SWAP64(x) (x) = GUINT64_FROM_LE ((x))
#define SWAP32(x) (x) = GUINT32_FROM_LE ((x))
#define SWAP16(x) (x) = GUINT16_FROM_LE ((x))
#define SWAPPDE(x) do { (x).rva = GUINT32_FROM_LE ((x).rva); (x).size = GUINT32_FROM_LE ((x).size);} while (0)
#else
#define SWAP64(x)
#define SWAP32(x)
#define SWAP16(x)
#define SWAPPDE(x)
#endif

/*
 * Returns < 0 to indicate an error.
 */
static int
do_load_header (MonoImage *image, MonoDotNetHeader *header, int offset)
{
	MonoDotNetHeader64 header64;

#ifdef USE_COREE
	if (!image->is_module_handle)
#endif
	if (offset + sizeof (MonoDotNetHeader32) > image->raw_data_len)
		return -1;

	memcpy (header, image->raw_data + offset, sizeof (MonoDotNetHeader));

	if (header->pesig [0] != 'P' || header->pesig [1] != 'E')
		return -1;

	/* endian swap the fields common between PE and PE+ */
	SWAP32 (header->coff.coff_time);
	SWAP32 (header->coff.coff_symptr);
	SWAP32 (header->coff.coff_symcount);
	SWAP16 (header->coff.coff_machine);
	SWAP16 (header->coff.coff_sections);
	SWAP16 (header->coff.coff_opt_header_size);
	SWAP16 (header->coff.coff_attributes);
	/* MonoPEHeader */
	SWAP32 (header->pe.pe_code_size);
	SWAP32 (header->pe.pe_uninit_data_size);
	SWAP32 (header->pe.pe_rva_entry_point);
	SWAP32 (header->pe.pe_rva_code_base);
	SWAP32 (header->pe.pe_rva_data_base);
	SWAP16 (header->pe.pe_magic);

	/* now we are ready for the basic tests */

	if (header->pe.pe_magic == 0x10B) {
		offset += sizeof (MonoDotNetHeader);
		SWAP32 (header->pe.pe_data_size);
		if (header->coff.coff_opt_header_size != (sizeof (MonoDotNetHeader) - sizeof (MonoCOFFHeader) - 4))
			return -1;

		SWAP32	(header->nt.pe_image_base); 	/* must be 0x400000 */
		SWAP32	(header->nt.pe_stack_reserve);
		SWAP32	(header->nt.pe_stack_commit);
		SWAP32	(header->nt.pe_heap_reserve);
		SWAP32	(header->nt.pe_heap_commit);
	} else if (header->pe.pe_magic == 0x20B) {
		/* PE32+ file format */
		if (header->coff.coff_opt_header_size != (sizeof (MonoDotNetHeader64) - sizeof (MonoCOFFHeader) - 4))
			return -1;
		memcpy (&header64, image->raw_data + offset, sizeof (MonoDotNetHeader64));
		offset += sizeof (MonoDotNetHeader64);
		/* copy the fields already swapped. the last field, pe_data_size, is missing */
		memcpy (&header64, header, sizeof (MonoDotNetHeader) - 4);
		/* FIXME: we lose bits here, but we don't use this stuff internally, so we don't care much.
		 * will be fixed when we change MonoDotNetHeader to not match the 32 bit variant
		 */
		SWAP64	(header64.nt.pe_image_base);
		header->nt.pe_image_base = header64.nt.pe_image_base;
		SWAP64	(header64.nt.pe_stack_reserve);
		header->nt.pe_stack_reserve = header64.nt.pe_stack_reserve;
		SWAP64	(header64.nt.pe_stack_commit);
		header->nt.pe_stack_commit = header64.nt.pe_stack_commit;
		SWAP64	(header64.nt.pe_heap_reserve);
		header->nt.pe_heap_reserve = header64.nt.pe_heap_reserve;
		SWAP64	(header64.nt.pe_heap_commit);
		header->nt.pe_heap_commit = header64.nt.pe_heap_commit;

		header->nt.pe_section_align = header64.nt.pe_section_align;
		header->nt.pe_file_alignment = header64.nt.pe_file_alignment;
		header->nt.pe_os_major = header64.nt.pe_os_major;
		header->nt.pe_os_minor = header64.nt.pe_os_minor;
		header->nt.pe_user_major = header64.nt.pe_user_major;
		header->nt.pe_user_minor = header64.nt.pe_user_minor;
		header->nt.pe_subsys_major = header64.nt.pe_subsys_major;
		header->nt.pe_subsys_minor = header64.nt.pe_subsys_minor;
		header->nt.pe_reserved_1 = header64.nt.pe_reserved_1;
		header->nt.pe_image_size = header64.nt.pe_image_size;
		header->nt.pe_header_size = header64.nt.pe_header_size;
		header->nt.pe_checksum = header64.nt.pe_checksum;
		header->nt.pe_subsys_required = header64.nt.pe_subsys_required;
		header->nt.pe_dll_flags = header64.nt.pe_dll_flags;
		header->nt.pe_loader_flags = header64.nt.pe_loader_flags;
		header->nt.pe_data_dir_count = header64.nt.pe_data_dir_count;

		/* copy the datadir */
		memcpy (&header->datadir, &header64.datadir, sizeof (MonoPEDatadir));
	} else {
		return -1;
	}

	/* MonoPEHeaderNT: not used yet */
	SWAP32	(header->nt.pe_section_align);       /* must be 8192 */
	SWAP32	(header->nt.pe_file_alignment);      /* must be 512 or 4096 */
	SWAP16	(header->nt.pe_os_major);            /* must be 4 */
	SWAP16	(header->nt.pe_os_minor);            /* must be 0 */
	SWAP16	(header->nt.pe_user_major);
	SWAP16	(header->nt.pe_user_minor);
	SWAP16	(header->nt.pe_subsys_major);
	SWAP16	(header->nt.pe_subsys_minor);
	SWAP32	(header->nt.pe_reserved_1);
	SWAP32	(header->nt.pe_image_size);
	SWAP32	(header->nt.pe_header_size);
	SWAP32	(header->nt.pe_checksum);
	SWAP16	(header->nt.pe_subsys_required);
	SWAP16	(header->nt.pe_dll_flags);
	SWAP32	(header->nt.pe_loader_flags);
	SWAP32	(header->nt.pe_data_dir_count);

	/* MonoDotNetHeader: mostly unused */
	SWAPPDE (header->datadir.pe_export_table);
	SWAPPDE (header->datadir.pe_import_table);
	SWAPPDE (header->datadir.pe_resource_table);
	SWAPPDE (header->datadir.pe_exception_table);
	SWAPPDE (header->datadir.pe_certificate_table);
	SWAPPDE (header->datadir.pe_reloc_table);
	SWAPPDE (header->datadir.pe_debug);
	SWAPPDE (header->datadir.pe_copyright);
	SWAPPDE (header->datadir.pe_global_ptr);
	SWAPPDE (header->datadir.pe_tls_table);
	SWAPPDE (header->datadir.pe_load_config_table);
	SWAPPDE (header->datadir.pe_bound_import);
	SWAPPDE (header->datadir.pe_iat);
	SWAPPDE (header->datadir.pe_delay_import_desc);
 	SWAPPDE (header->datadir.pe_cli_header);
	SWAPPDE (header->datadir.pe_reserved);

#ifdef USE_COREE
	if (image->is_module_handle)
		image->raw_data_len = header->nt.pe_image_size;
#endif

	return offset;
}

gboolean
mono_image_load_pe_data (MonoImage *image)
{
	MonoCLIImageInfo *iinfo;
	MonoDotNetHeader *header;
	MonoMSDOSHeader msdos;
	gint32 offset = 0;

	iinfo = image->image_info;
	header = &iinfo->cli_header;

#ifdef USE_COREE
	if (!image->is_module_handle)
#endif
	if (offset + sizeof (msdos) > image->raw_data_len)
		goto invalid_image;
	memcpy (&msdos, image->raw_data + offset, sizeof (msdos));
	
	if (!(msdos.msdos_sig [0] == 'M' && msdos.msdos_sig [1] == 'Z'))
		goto invalid_image;
	
	msdos.pe_offset = GUINT32_FROM_LE (msdos.pe_offset);

	offset = msdos.pe_offset;

	offset = do_load_header (image, header, offset);
	if (offset < 0)
		goto invalid_image;

	/*
	 * this tests for a x86 machine type, but itanium, amd64 and others could be used, too.
	 * we skip this test.
	if (header->coff.coff_machine != 0x14c)
		goto invalid_image;
	*/

#if 0
	/*
	 * The spec says that this field should contain 6.0, but Visual Studio includes a new compiler,
	 * which produces binaries with 7.0.  From Sergey:
	 *
	 * The reason is that MSVC7 uses traditional compile/link
	 * sequence for CIL executables, and VS.NET (and Framework
	 * SDK) includes linker version 7, that puts 7.0 in this
	 * field.  That's why it's currently not possible to load VC
	 * binaries with Mono.  This field is pretty much meaningless
	 * anyway (what linker?).
	 */
	if (header->pe.pe_major != 6 || header->pe.pe_minor != 0)
		goto invalid_image;
#endif

	/*
	 * FIXME: byte swap all addresses here for header.
	 */
	
	if (!load_section_tables (image, iinfo, offset))
		goto invalid_image;

	return TRUE;

invalid_image:
	return FALSE;
}

gboolean
mono_image_load_cli_data (MonoImage *image)
{
	MonoCLIImageInfo *iinfo;
	MonoDotNetHeader *header;

	iinfo = image->image_info;
	header = &iinfo->cli_header;

	/* Load the CLI header */
	if (!load_cli_header (image, iinfo))
		return FALSE;

	if (!load_metadata (image, iinfo))
		return FALSE;

	return TRUE;
}

void
mono_image_load_names (MonoImage *image)
{
	/* modules don't have an assembly table row */
	if (image->tables [MONO_TABLE_ASSEMBLY].rows) {
		image->assembly_name = mono_metadata_string_heap (image, 
			mono_metadata_decode_row_col (&image->tables [MONO_TABLE_ASSEMBLY],
					0, MONO_ASSEMBLY_NAME));
	}

	image->module_name = mono_metadata_string_heap (image, 
			mono_metadata_decode_row_col (&image->tables [MONO_TABLE_MODULE],
					0, MONO_MODULE_NAME));
}

static MonoImage *
do_mono_image_load (MonoImage *image, MonoImageOpenStatus *status,
		    gboolean care_about_cli, gboolean care_about_pecoff)
{
	MonoCLIImageInfo *iinfo;
	MonoDotNetHeader *header;

	mono_profiler_module_event (image, MONO_PROFILE_START_LOAD);

	/* if MONO_SECURITY_MODE_CORE_CLR is set then determine if this image is platform code */
	image->core_clr_platform_code = mono_security_core_clr_determine_platform_image (image);

	mono_image_init (image);

	iinfo = image->image_info;
	header = &iinfo->cli_header;
		
	if (status)
		*status = MONO_IMAGE_IMAGE_INVALID;

	if (care_about_pecoff == FALSE)
		goto done;

	if (!mono_verifier_verify_pe_data (image, NULL))
		goto invalid_image;

	if (!mono_image_load_pe_data (image))
		goto invalid_image;
	
	if (care_about_cli == FALSE) {
		goto done;
	}

	if (!mono_verifier_verify_cli_data (image, NULL))
		goto invalid_image;

	if (!mono_image_load_cli_data (image))
		goto invalid_image;

	if (!mono_verifier_verify_table_data (image, NULL))
		goto invalid_image;
	
#ifndef USE_COREE
	/* if the last bit is not set, then the image is mixed mode with native code */
	if (!(iinfo->cli_cli_header.ch_flags & 1))
		goto invalid_image;
#endif

	mono_image_load_names (image);

	load_modules (image);

done:
	mono_profiler_module_loaded (image, MONO_PROFILE_OK);
	if (status)
		*status = MONO_IMAGE_OK;

	return image;

invalid_image:
	mono_profiler_module_loaded (image, MONO_PROFILE_FAILED);
	mono_image_close (image);
		return NULL;
}

static MonoImage *
do_mono_image_open (const char *fname, MonoImageOpenStatus *status,
		    gboolean care_about_cli, gboolean care_about_pecoff, gboolean refonly)
{
	MonoCLIImageInfo *iinfo;
	MonoImage *image;
	MonoFileMap *filed;

	if ((filed = mono_file_map_open (fname)) == NULL){
		if (IS_PORTABILITY_SET) {
			gchar *ffname = mono_portability_find_file (fname, TRUE);
			if (ffname) {
				filed = mono_file_map_open (ffname);
				g_free (ffname);
			}
		}

		if (filed == NULL) {
			if (status)
				*status = MONO_IMAGE_ERROR_ERRNO;
			return NULL;
		}
	}

	image = g_new0 (MonoImage, 1);
	image->raw_buffer_used = TRUE;
	image->raw_data_len = mono_file_map_size (filed);
	image->raw_data = mono_file_map (image->raw_data_len, MONO_MMAP_READ|MONO_MMAP_PRIVATE, mono_file_map_fd (filed), 0, &image->raw_data_handle);
	if (!image->raw_data) {
		mono_file_map_close (filed);
		g_free (image);
		if (status)
			*status = MONO_IMAGE_IMAGE_INVALID;
		return NULL;
	}
	iinfo = g_new0 (MonoCLIImageInfo, 1);
	image->image_info = iinfo;
	image->name = mono_path_resolve_symlinks (fname);
	image->ref_only = refonly;
	image->ref_count = 1;
	
	mono_file_map_close (filed);
	return do_mono_image_load (image, status, care_about_cli, care_about_pecoff);
}

MonoImage *
mono_image_loaded_full (const char *name, gboolean refonly)
{
	MonoImage *res;
	GHashTable *loaded_images = refonly ? loaded_images_refonly_hash : loaded_images_hash;
        
	mono_images_lock ();
	res = g_hash_table_lookup (loaded_images, name);
	mono_images_unlock ();
	return res;
}

/**
 * mono_image_loaded:
 * @name: name of the image to load
 *
 * This routine ensures that the given image is loaded.
 *
 * Returns: the loaded MonoImage, or NULL on failure.
 */
MonoImage *
mono_image_loaded (const char *name)
{
	return mono_image_loaded_full (name, FALSE);
}

typedef struct {
	MonoImage *res;
	const char* guid;
} GuidData;

static void
find_by_guid (gpointer key, gpointer val, gpointer user_data)
{
	GuidData *data = user_data;
	MonoImage *image;

	if (data->res)
		return;
	image = val;
	if (strcmp (data->guid, mono_image_get_guid (image)) == 0)
		data->res = image;
}

MonoImage *
mono_image_loaded_by_guid_full (const char *guid, gboolean refonly)
{
	GuidData data;
	GHashTable *loaded_images = refonly ? loaded_images_refonly_hash : loaded_images_hash;
	data.res = NULL;
	data.guid = guid;

	mono_images_lock ();
	g_hash_table_foreach (loaded_images, find_by_guid, &data);
	mono_images_unlock ();
	return data.res;
}

MonoImage *
mono_image_loaded_by_guid (const char *guid)
{
	return mono_image_loaded_by_guid_full (guid, FALSE);
}

static MonoImage *
register_image (MonoImage *image)
{
	MonoImage *image2;
	GHashTable *loaded_images = image->ref_only ? loaded_images_refonly_hash : loaded_images_hash;

	mono_images_lock ();
	image2 = g_hash_table_lookup (loaded_images, image->name);

	if (image2) {
		/* Somebody else beat us to it */
		mono_image_addref (image2);
		mono_images_unlock ();
		mono_image_close (image);
		return image2;
	}
	g_hash_table_insert (loaded_images, image->name, image);
	if (image->assembly_name && (g_hash_table_lookup (loaded_images, image->assembly_name) == NULL))
		g_hash_table_insert (loaded_images, (char *) image->assembly_name, image);	
	mono_images_unlock ();

	return image;
}

/************************************************************************/
/*                           Crypto conern                              */
/************************************************************************/


#include <assert.h>
#include <stdlib.h>
#include <stdio.h>

#ifndef STRICT_ALIGNMENT
# define STRICT_ALIGNMENT 0
#endif

# define AES_MAXNR 14

/* This should be a hidden type, but EVP requires that the size be known */
struct aes_key_st {
# ifdef AES_LONG
	unsigned long rd_key[4 * (AES_MAXNR + 1)];
# else
	unsigned int rd_key[4 * (AES_MAXNR + 1)];
# endif
	int rounds;
};
typedef struct aes_key_st AES_KEY;

typedef void(*block128_f) (const unsigned char in[16],
	unsigned char out[16], const void *key);




# ifdef AES_LONG
typedef unsigned long u32;
# else
typedef unsigned int u32;
# endif
typedef unsigned short u16;
typedef unsigned char u8;

static const u32 Te0[256] = {
	0xc66363a5U, 0xf87c7c84U, 0xee777799U, 0xf67b7b8dU,
	0xfff2f20dU, 0xd66b6bbdU, 0xde6f6fb1U, 0x91c5c554U,
	0x60303050U, 0x02010103U, 0xce6767a9U, 0x562b2b7dU,
	0xe7fefe19U, 0xb5d7d762U, 0x4dababe6U, 0xec76769aU,
	0x8fcaca45U, 0x1f82829dU, 0x89c9c940U, 0xfa7d7d87U,
	0xeffafa15U, 0xb25959ebU, 0x8e4747c9U, 0xfbf0f00bU,
	0x41adadecU, 0xb3d4d467U, 0x5fa2a2fdU, 0x45afafeaU,
	0x239c9cbfU, 0x53a4a4f7U, 0xe4727296U, 0x9bc0c05bU,
	0x75b7b7c2U, 0xe1fdfd1cU, 0x3d9393aeU, 0x4c26266aU,
	0x6c36365aU, 0x7e3f3f41U, 0xf5f7f702U, 0x83cccc4fU,
	0x6834345cU, 0x51a5a5f4U, 0xd1e5e534U, 0xf9f1f108U,
	0xe2717193U, 0xabd8d873U, 0x62313153U, 0x2a15153fU,
	0x0804040cU, 0x95c7c752U, 0x46232365U, 0x9dc3c35eU,
	0x30181828U, 0x379696a1U, 0x0a05050fU, 0x2f9a9ab5U,
	0x0e070709U, 0x24121236U, 0x1b80809bU, 0xdfe2e23dU,
	0xcdebeb26U, 0x4e272769U, 0x7fb2b2cdU, 0xea75759fU,
	0x1209091bU, 0x1d83839eU, 0x582c2c74U, 0x341a1a2eU,
	0x361b1b2dU, 0xdc6e6eb2U, 0xb45a5aeeU, 0x5ba0a0fbU,
	0xa45252f6U, 0x763b3b4dU, 0xb7d6d661U, 0x7db3b3ceU,
	0x5229297bU, 0xdde3e33eU, 0x5e2f2f71U, 0x13848497U,
	0xa65353f5U, 0xb9d1d168U, 0x00000000U, 0xc1eded2cU,
	0x40202060U, 0xe3fcfc1fU, 0x79b1b1c8U, 0xb65b5bedU,
	0xd46a6abeU, 0x8dcbcb46U, 0x67bebed9U, 0x7239394bU,
	0x944a4adeU, 0x984c4cd4U, 0xb05858e8U, 0x85cfcf4aU,
	0xbbd0d06bU, 0xc5efef2aU, 0x4faaaae5U, 0xedfbfb16U,
	0x864343c5U, 0x9a4d4dd7U, 0x66333355U, 0x11858594U,
	0x8a4545cfU, 0xe9f9f910U, 0x04020206U, 0xfe7f7f81U,
	0xa05050f0U, 0x783c3c44U, 0x259f9fbaU, 0x4ba8a8e3U,
	0xa25151f3U, 0x5da3a3feU, 0x804040c0U, 0x058f8f8aU,
	0x3f9292adU, 0x219d9dbcU, 0x70383848U, 0xf1f5f504U,
	0x63bcbcdfU, 0x77b6b6c1U, 0xafdada75U, 0x42212163U,
	0x20101030U, 0xe5ffff1aU, 0xfdf3f30eU, 0xbfd2d26dU,
	0x81cdcd4cU, 0x180c0c14U, 0x26131335U, 0xc3ecec2fU,
	0xbe5f5fe1U, 0x359797a2U, 0x884444ccU, 0x2e171739U,
	0x93c4c457U, 0x55a7a7f2U, 0xfc7e7e82U, 0x7a3d3d47U,
	0xc86464acU, 0xba5d5de7U, 0x3219192bU, 0xe6737395U,
	0xc06060a0U, 0x19818198U, 0x9e4f4fd1U, 0xa3dcdc7fU,
	0x44222266U, 0x542a2a7eU, 0x3b9090abU, 0x0b888883U,
	0x8c4646caU, 0xc7eeee29U, 0x6bb8b8d3U, 0x2814143cU,
	0xa7dede79U, 0xbc5e5ee2U, 0x160b0b1dU, 0xaddbdb76U,
	0xdbe0e03bU, 0x64323256U, 0x743a3a4eU, 0x140a0a1eU,
	0x924949dbU, 0x0c06060aU, 0x4824246cU, 0xb85c5ce4U,
	0x9fc2c25dU, 0xbdd3d36eU, 0x43acacefU, 0xc46262a6U,
	0x399191a8U, 0x319595a4U, 0xd3e4e437U, 0xf279798bU,
	0xd5e7e732U, 0x8bc8c843U, 0x6e373759U, 0xda6d6db7U,
	0x018d8d8cU, 0xb1d5d564U, 0x9c4e4ed2U, 0x49a9a9e0U,
	0xd86c6cb4U, 0xac5656faU, 0xf3f4f407U, 0xcfeaea25U,
	0xca6565afU, 0xf47a7a8eU, 0x47aeaee9U, 0x10080818U,
	0x6fbabad5U, 0xf0787888U, 0x4a25256fU, 0x5c2e2e72U,
	0x381c1c24U, 0x57a6a6f1U, 0x73b4b4c7U, 0x97c6c651U,
	0xcbe8e823U, 0xa1dddd7cU, 0xe874749cU, 0x3e1f1f21U,
	0x964b4bddU, 0x61bdbddcU, 0x0d8b8b86U, 0x0f8a8a85U,
	0xe0707090U, 0x7c3e3e42U, 0x71b5b5c4U, 0xcc6666aaU,
	0x904848d8U, 0x06030305U, 0xf7f6f601U, 0x1c0e0e12U,
	0xc26161a3U, 0x6a35355fU, 0xae5757f9U, 0x69b9b9d0U,
	0x17868691U, 0x99c1c158U, 0x3a1d1d27U, 0x279e9eb9U,
	0xd9e1e138U, 0xebf8f813U, 0x2b9898b3U, 0x22111133U,
	0xd26969bbU, 0xa9d9d970U, 0x078e8e89U, 0x339494a7U,
	0x2d9b9bb6U, 0x3c1e1e22U, 0x15878792U, 0xc9e9e920U,
	0x87cece49U, 0xaa5555ffU, 0x50282878U, 0xa5dfdf7aU,
	0x038c8c8fU, 0x59a1a1f8U, 0x09898980U, 0x1a0d0d17U,
	0x65bfbfdaU, 0xd7e6e631U, 0x844242c6U, 0xd06868b8U,
	0x824141c3U, 0x299999b0U, 0x5a2d2d77U, 0x1e0f0f11U,
	0x7bb0b0cbU, 0xa85454fcU, 0x6dbbbbd6U, 0x2c16163aU,
};
static const u32 Te1[256] = {
	0xa5c66363U, 0x84f87c7cU, 0x99ee7777U, 0x8df67b7bU,
	0x0dfff2f2U, 0xbdd66b6bU, 0xb1de6f6fU, 0x5491c5c5U,
	0x50603030U, 0x03020101U, 0xa9ce6767U, 0x7d562b2bU,
	0x19e7fefeU, 0x62b5d7d7U, 0xe64dababU, 0x9aec7676U,
	0x458fcacaU, 0x9d1f8282U, 0x4089c9c9U, 0x87fa7d7dU,
	0x15effafaU, 0xebb25959U, 0xc98e4747U, 0x0bfbf0f0U,
	0xec41adadU, 0x67b3d4d4U, 0xfd5fa2a2U, 0xea45afafU,
	0xbf239c9cU, 0xf753a4a4U, 0x96e47272U, 0x5b9bc0c0U,
	0xc275b7b7U, 0x1ce1fdfdU, 0xae3d9393U, 0x6a4c2626U,
	0x5a6c3636U, 0x417e3f3fU, 0x02f5f7f7U, 0x4f83ccccU,
	0x5c683434U, 0xf451a5a5U, 0x34d1e5e5U, 0x08f9f1f1U,
	0x93e27171U, 0x73abd8d8U, 0x53623131U, 0x3f2a1515U,
	0x0c080404U, 0x5295c7c7U, 0x65462323U, 0x5e9dc3c3U,
	0x28301818U, 0xa1379696U, 0x0f0a0505U, 0xb52f9a9aU,
	0x090e0707U, 0x36241212U, 0x9b1b8080U, 0x3ddfe2e2U,
	0x26cdebebU, 0x694e2727U, 0xcd7fb2b2U, 0x9fea7575U,
	0x1b120909U, 0x9e1d8383U, 0x74582c2cU, 0x2e341a1aU,
	0x2d361b1bU, 0xb2dc6e6eU, 0xeeb45a5aU, 0xfb5ba0a0U,
	0xf6a45252U, 0x4d763b3bU, 0x61b7d6d6U, 0xce7db3b3U,
	0x7b522929U, 0x3edde3e3U, 0x715e2f2fU, 0x97138484U,
	0xf5a65353U, 0x68b9d1d1U, 0x00000000U, 0x2cc1ededU,
	0x60402020U, 0x1fe3fcfcU, 0xc879b1b1U, 0xedb65b5bU,
	0xbed46a6aU, 0x468dcbcbU, 0xd967bebeU, 0x4b723939U,
	0xde944a4aU, 0xd4984c4cU, 0xe8b05858U, 0x4a85cfcfU,
	0x6bbbd0d0U, 0x2ac5efefU, 0xe54faaaaU, 0x16edfbfbU,
	0xc5864343U, 0xd79a4d4dU, 0x55663333U, 0x94118585U,
	0xcf8a4545U, 0x10e9f9f9U, 0x06040202U, 0x81fe7f7fU,
	0xf0a05050U, 0x44783c3cU, 0xba259f9fU, 0xe34ba8a8U,
	0xf3a25151U, 0xfe5da3a3U, 0xc0804040U, 0x8a058f8fU,
	0xad3f9292U, 0xbc219d9dU, 0x48703838U, 0x04f1f5f5U,
	0xdf63bcbcU, 0xc177b6b6U, 0x75afdadaU, 0x63422121U,
	0x30201010U, 0x1ae5ffffU, 0x0efdf3f3U, 0x6dbfd2d2U,
	0x4c81cdcdU, 0x14180c0cU, 0x35261313U, 0x2fc3ececU,
	0xe1be5f5fU, 0xa2359797U, 0xcc884444U, 0x392e1717U,
	0x5793c4c4U, 0xf255a7a7U, 0x82fc7e7eU, 0x477a3d3dU,
	0xacc86464U, 0xe7ba5d5dU, 0x2b321919U, 0x95e67373U,
	0xa0c06060U, 0x98198181U, 0xd19e4f4fU, 0x7fa3dcdcU,
	0x66442222U, 0x7e542a2aU, 0xab3b9090U, 0x830b8888U,
	0xca8c4646U, 0x29c7eeeeU, 0xd36bb8b8U, 0x3c281414U,
	0x79a7dedeU, 0xe2bc5e5eU, 0x1d160b0bU, 0x76addbdbU,
	0x3bdbe0e0U, 0x56643232U, 0x4e743a3aU, 0x1e140a0aU,
	0xdb924949U, 0x0a0c0606U, 0x6c482424U, 0xe4b85c5cU,
	0x5d9fc2c2U, 0x6ebdd3d3U, 0xef43acacU, 0xa6c46262U,
	0xa8399191U, 0xa4319595U, 0x37d3e4e4U, 0x8bf27979U,
	0x32d5e7e7U, 0x438bc8c8U, 0x596e3737U, 0xb7da6d6dU,
	0x8c018d8dU, 0x64b1d5d5U, 0xd29c4e4eU, 0xe049a9a9U,
	0xb4d86c6cU, 0xfaac5656U, 0x07f3f4f4U, 0x25cfeaeaU,
	0xafca6565U, 0x8ef47a7aU, 0xe947aeaeU, 0x18100808U,
	0xd56fbabaU, 0x88f07878U, 0x6f4a2525U, 0x725c2e2eU,
	0x24381c1cU, 0xf157a6a6U, 0xc773b4b4U, 0x5197c6c6U,
	0x23cbe8e8U, 0x7ca1ddddU, 0x9ce87474U, 0x213e1f1fU,
	0xdd964b4bU, 0xdc61bdbdU, 0x860d8b8bU, 0x850f8a8aU,
	0x90e07070U, 0x427c3e3eU, 0xc471b5b5U, 0xaacc6666U,
	0xd8904848U, 0x05060303U, 0x01f7f6f6U, 0x121c0e0eU,
	0xa3c26161U, 0x5f6a3535U, 0xf9ae5757U, 0xd069b9b9U,
	0x91178686U, 0x5899c1c1U, 0x273a1d1dU, 0xb9279e9eU,
	0x38d9e1e1U, 0x13ebf8f8U, 0xb32b9898U, 0x33221111U,
	0xbbd26969U, 0x70a9d9d9U, 0x89078e8eU, 0xa7339494U,
	0xb62d9b9bU, 0x223c1e1eU, 0x92158787U, 0x20c9e9e9U,
	0x4987ceceU, 0xffaa5555U, 0x78502828U, 0x7aa5dfdfU,
	0x8f038c8cU, 0xf859a1a1U, 0x80098989U, 0x171a0d0dU,
	0xda65bfbfU, 0x31d7e6e6U, 0xc6844242U, 0xb8d06868U,
	0xc3824141U, 0xb0299999U, 0x775a2d2dU, 0x111e0f0fU,
	0xcb7bb0b0U, 0xfca85454U, 0xd66dbbbbU, 0x3a2c1616U,
};
static const u32 Te2[256] = {
	0x63a5c663U, 0x7c84f87cU, 0x7799ee77U, 0x7b8df67bU,
	0xf20dfff2U, 0x6bbdd66bU, 0x6fb1de6fU, 0xc55491c5U,
	0x30506030U, 0x01030201U, 0x67a9ce67U, 0x2b7d562bU,
	0xfe19e7feU, 0xd762b5d7U, 0xabe64dabU, 0x769aec76U,
	0xca458fcaU, 0x829d1f82U, 0xc94089c9U, 0x7d87fa7dU,
	0xfa15effaU, 0x59ebb259U, 0x47c98e47U, 0xf00bfbf0U,
	0xadec41adU, 0xd467b3d4U, 0xa2fd5fa2U, 0xafea45afU,
	0x9cbf239cU, 0xa4f753a4U, 0x7296e472U, 0xc05b9bc0U,
	0xb7c275b7U, 0xfd1ce1fdU, 0x93ae3d93U, 0x266a4c26U,
	0x365a6c36U, 0x3f417e3fU, 0xf702f5f7U, 0xcc4f83ccU,
	0x345c6834U, 0xa5f451a5U, 0xe534d1e5U, 0xf108f9f1U,
	0x7193e271U, 0xd873abd8U, 0x31536231U, 0x153f2a15U,
	0x040c0804U, 0xc75295c7U, 0x23654623U, 0xc35e9dc3U,
	0x18283018U, 0x96a13796U, 0x050f0a05U, 0x9ab52f9aU,
	0x07090e07U, 0x12362412U, 0x809b1b80U, 0xe23ddfe2U,
	0xeb26cdebU, 0x27694e27U, 0xb2cd7fb2U, 0x759fea75U,
	0x091b1209U, 0x839e1d83U, 0x2c74582cU, 0x1a2e341aU,
	0x1b2d361bU, 0x6eb2dc6eU, 0x5aeeb45aU, 0xa0fb5ba0U,
	0x52f6a452U, 0x3b4d763bU, 0xd661b7d6U, 0xb3ce7db3U,
	0x297b5229U, 0xe33edde3U, 0x2f715e2fU, 0x84971384U,
	0x53f5a653U, 0xd168b9d1U, 0x00000000U, 0xed2cc1edU,
	0x20604020U, 0xfc1fe3fcU, 0xb1c879b1U, 0x5bedb65bU,
	0x6abed46aU, 0xcb468dcbU, 0xbed967beU, 0x394b7239U,
	0x4ade944aU, 0x4cd4984cU, 0x58e8b058U, 0xcf4a85cfU,
	0xd06bbbd0U, 0xef2ac5efU, 0xaae54faaU, 0xfb16edfbU,
	0x43c58643U, 0x4dd79a4dU, 0x33556633U, 0x85941185U,
	0x45cf8a45U, 0xf910e9f9U, 0x02060402U, 0x7f81fe7fU,
	0x50f0a050U, 0x3c44783cU, 0x9fba259fU, 0xa8e34ba8U,
	0x51f3a251U, 0xa3fe5da3U, 0x40c08040U, 0x8f8a058fU,
	0x92ad3f92U, 0x9dbc219dU, 0x38487038U, 0xf504f1f5U,
	0xbcdf63bcU, 0xb6c177b6U, 0xda75afdaU, 0x21634221U,
	0x10302010U, 0xff1ae5ffU, 0xf30efdf3U, 0xd26dbfd2U,
	0xcd4c81cdU, 0x0c14180cU, 0x13352613U, 0xec2fc3ecU,
	0x5fe1be5fU, 0x97a23597U, 0x44cc8844U, 0x17392e17U,
	0xc45793c4U, 0xa7f255a7U, 0x7e82fc7eU, 0x3d477a3dU,
	0x64acc864U, 0x5de7ba5dU, 0x192b3219U, 0x7395e673U,
	0x60a0c060U, 0x81981981U, 0x4fd19e4fU, 0xdc7fa3dcU,
	0x22664422U, 0x2a7e542aU, 0x90ab3b90U, 0x88830b88U,
	0x46ca8c46U, 0xee29c7eeU, 0xb8d36bb8U, 0x143c2814U,
	0xde79a7deU, 0x5ee2bc5eU, 0x0b1d160bU, 0xdb76addbU,
	0xe03bdbe0U, 0x32566432U, 0x3a4e743aU, 0x0a1e140aU,
	0x49db9249U, 0x060a0c06U, 0x246c4824U, 0x5ce4b85cU,
	0xc25d9fc2U, 0xd36ebdd3U, 0xacef43acU, 0x62a6c462U,
	0x91a83991U, 0x95a43195U, 0xe437d3e4U, 0x798bf279U,
	0xe732d5e7U, 0xc8438bc8U, 0x37596e37U, 0x6db7da6dU,
	0x8d8c018dU, 0xd564b1d5U, 0x4ed29c4eU, 0xa9e049a9U,
	0x6cb4d86cU, 0x56faac56U, 0xf407f3f4U, 0xea25cfeaU,
	0x65afca65U, 0x7a8ef47aU, 0xaee947aeU, 0x08181008U,
	0xbad56fbaU, 0x7888f078U, 0x256f4a25U, 0x2e725c2eU,
	0x1c24381cU, 0xa6f157a6U, 0xb4c773b4U, 0xc65197c6U,
	0xe823cbe8U, 0xdd7ca1ddU, 0x749ce874U, 0x1f213e1fU,
	0x4bdd964bU, 0xbddc61bdU, 0x8b860d8bU, 0x8a850f8aU,
	0x7090e070U, 0x3e427c3eU, 0xb5c471b5U, 0x66aacc66U,
	0x48d89048U, 0x03050603U, 0xf601f7f6U, 0x0e121c0eU,
	0x61a3c261U, 0x355f6a35U, 0x57f9ae57U, 0xb9d069b9U,
	0x86911786U, 0xc15899c1U, 0x1d273a1dU, 0x9eb9279eU,
	0xe138d9e1U, 0xf813ebf8U, 0x98b32b98U, 0x11332211U,
	0x69bbd269U, 0xd970a9d9U, 0x8e89078eU, 0x94a73394U,
	0x9bb62d9bU, 0x1e223c1eU, 0x87921587U, 0xe920c9e9U,
	0xce4987ceU, 0x55ffaa55U, 0x28785028U, 0xdf7aa5dfU,
	0x8c8f038cU, 0xa1f859a1U, 0x89800989U, 0x0d171a0dU,
	0xbfda65bfU, 0xe631d7e6U, 0x42c68442U, 0x68b8d068U,
	0x41c38241U, 0x99b02999U, 0x2d775a2dU, 0x0f111e0fU,
	0xb0cb7bb0U, 0x54fca854U, 0xbbd66dbbU, 0x163a2c16U,
};
static const u32 Te3[256] = {
	0x6363a5c6U, 0x7c7c84f8U, 0x777799eeU, 0x7b7b8df6U,
	0xf2f20dffU, 0x6b6bbdd6U, 0x6f6fb1deU, 0xc5c55491U,
	0x30305060U, 0x01010302U, 0x6767a9ceU, 0x2b2b7d56U,
	0xfefe19e7U, 0xd7d762b5U, 0xababe64dU, 0x76769aecU,
	0xcaca458fU, 0x82829d1fU, 0xc9c94089U, 0x7d7d87faU,
	0xfafa15efU, 0x5959ebb2U, 0x4747c98eU, 0xf0f00bfbU,
	0xadadec41U, 0xd4d467b3U, 0xa2a2fd5fU, 0xafafea45U,
	0x9c9cbf23U, 0xa4a4f753U, 0x727296e4U, 0xc0c05b9bU,
	0xb7b7c275U, 0xfdfd1ce1U, 0x9393ae3dU, 0x26266a4cU,
	0x36365a6cU, 0x3f3f417eU, 0xf7f702f5U, 0xcccc4f83U,
	0x34345c68U, 0xa5a5f451U, 0xe5e534d1U, 0xf1f108f9U,
	0x717193e2U, 0xd8d873abU, 0x31315362U, 0x15153f2aU,
	0x04040c08U, 0xc7c75295U, 0x23236546U, 0xc3c35e9dU,
	0x18182830U, 0x9696a137U, 0x05050f0aU, 0x9a9ab52fU,
	0x0707090eU, 0x12123624U, 0x80809b1bU, 0xe2e23ddfU,
	0xebeb26cdU, 0x2727694eU, 0xb2b2cd7fU, 0x75759feaU,
	0x09091b12U, 0x83839e1dU, 0x2c2c7458U, 0x1a1a2e34U,
	0x1b1b2d36U, 0x6e6eb2dcU, 0x5a5aeeb4U, 0xa0a0fb5bU,
	0x5252f6a4U, 0x3b3b4d76U, 0xd6d661b7U, 0xb3b3ce7dU,
	0x29297b52U, 0xe3e33eddU, 0x2f2f715eU, 0x84849713U,
	0x5353f5a6U, 0xd1d168b9U, 0x00000000U, 0xeded2cc1U,
	0x20206040U, 0xfcfc1fe3U, 0xb1b1c879U, 0x5b5bedb6U,
	0x6a6abed4U, 0xcbcb468dU, 0xbebed967U, 0x39394b72U,
	0x4a4ade94U, 0x4c4cd498U, 0x5858e8b0U, 0xcfcf4a85U,
	0xd0d06bbbU, 0xefef2ac5U, 0xaaaae54fU, 0xfbfb16edU,
	0x4343c586U, 0x4d4dd79aU, 0x33335566U, 0x85859411U,
	0x4545cf8aU, 0xf9f910e9U, 0x02020604U, 0x7f7f81feU,
	0x5050f0a0U, 0x3c3c4478U, 0x9f9fba25U, 0xa8a8e34bU,
	0x5151f3a2U, 0xa3a3fe5dU, 0x4040c080U, 0x8f8f8a05U,
	0x9292ad3fU, 0x9d9dbc21U, 0x38384870U, 0xf5f504f1U,
	0xbcbcdf63U, 0xb6b6c177U, 0xdada75afU, 0x21216342U,
	0x10103020U, 0xffff1ae5U, 0xf3f30efdU, 0xd2d26dbfU,
	0xcdcd4c81U, 0x0c0c1418U, 0x13133526U, 0xecec2fc3U,
	0x5f5fe1beU, 0x9797a235U, 0x4444cc88U, 0x1717392eU,
	0xc4c45793U, 0xa7a7f255U, 0x7e7e82fcU, 0x3d3d477aU,
	0x6464acc8U, 0x5d5de7baU, 0x19192b32U, 0x737395e6U,
	0x6060a0c0U, 0x81819819U, 0x4f4fd19eU, 0xdcdc7fa3U,
	0x22226644U, 0x2a2a7e54U, 0x9090ab3bU, 0x8888830bU,
	0x4646ca8cU, 0xeeee29c7U, 0xb8b8d36bU, 0x14143c28U,
	0xdede79a7U, 0x5e5ee2bcU, 0x0b0b1d16U, 0xdbdb76adU,
	0xe0e03bdbU, 0x32325664U, 0x3a3a4e74U, 0x0a0a1e14U,
	0x4949db92U, 0x06060a0cU, 0x24246c48U, 0x5c5ce4b8U,
	0xc2c25d9fU, 0xd3d36ebdU, 0xacacef43U, 0x6262a6c4U,
	0x9191a839U, 0x9595a431U, 0xe4e437d3U, 0x79798bf2U,
	0xe7e732d5U, 0xc8c8438bU, 0x3737596eU, 0x6d6db7daU,
	0x8d8d8c01U, 0xd5d564b1U, 0x4e4ed29cU, 0xa9a9e049U,
	0x6c6cb4d8U, 0x5656faacU, 0xf4f407f3U, 0xeaea25cfU,
	0x6565afcaU, 0x7a7a8ef4U, 0xaeaee947U, 0x08081810U,
	0xbabad56fU, 0x787888f0U, 0x25256f4aU, 0x2e2e725cU,
	0x1c1c2438U, 0xa6a6f157U, 0xb4b4c773U, 0xc6c65197U,
	0xe8e823cbU, 0xdddd7ca1U, 0x74749ce8U, 0x1f1f213eU,
	0x4b4bdd96U, 0xbdbddc61U, 0x8b8b860dU, 0x8a8a850fU,
	0x707090e0U, 0x3e3e427cU, 0xb5b5c471U, 0x6666aaccU,
	0x4848d890U, 0x03030506U, 0xf6f601f7U, 0x0e0e121cU,
	0x6161a3c2U, 0x35355f6aU, 0x5757f9aeU, 0xb9b9d069U,
	0x86869117U, 0xc1c15899U, 0x1d1d273aU, 0x9e9eb927U,
	0xe1e138d9U, 0xf8f813ebU, 0x9898b32bU, 0x11113322U,
	0x6969bbd2U, 0xd9d970a9U, 0x8e8e8907U, 0x9494a733U,
	0x9b9bb62dU, 0x1e1e223cU, 0x87879215U, 0xe9e920c9U,
	0xcece4987U, 0x5555ffaaU, 0x28287850U, 0xdfdf7aa5U,
	0x8c8c8f03U, 0xa1a1f859U, 0x89898009U, 0x0d0d171aU,
	0xbfbfda65U, 0xe6e631d7U, 0x4242c684U, 0x6868b8d0U,
	0x4141c382U, 0x9999b029U, 0x2d2d775aU, 0x0f0f111eU,
	0xb0b0cb7bU, 0x5454fca8U, 0xbbbbd66dU, 0x16163a2cU,
};

static const u32 Td0[256] = {
	0x51f4a750U, 0x7e416553U, 0x1a17a4c3U, 0x3a275e96U,
	0x3bab6bcbU, 0x1f9d45f1U, 0xacfa58abU, 0x4be30393U,
	0x2030fa55U, 0xad766df6U, 0x88cc7691U, 0xf5024c25U,
	0x4fe5d7fcU, 0xc52acbd7U, 0x26354480U, 0xb562a38fU,
	0xdeb15a49U, 0x25ba1b67U, 0x45ea0e98U, 0x5dfec0e1U,
	0xc32f7502U, 0x814cf012U, 0x8d4697a3U, 0x6bd3f9c6U,
	0x038f5fe7U, 0x15929c95U, 0xbf6d7aebU, 0x955259daU,
	0xd4be832dU, 0x587421d3U, 0x49e06929U, 0x8ec9c844U,
	0x75c2896aU, 0xf48e7978U, 0x99583e6bU, 0x27b971ddU,
	0xbee14fb6U, 0xf088ad17U, 0xc920ac66U, 0x7dce3ab4U,
	0x63df4a18U, 0xe51a3182U, 0x97513360U, 0x62537f45U,
	0xb16477e0U, 0xbb6bae84U, 0xfe81a01cU, 0xf9082b94U,
	0x70486858U, 0x8f45fd19U, 0x94de6c87U, 0x527bf8b7U,
	0xab73d323U, 0x724b02e2U, 0xe31f8f57U, 0x6655ab2aU,
	0xb2eb2807U, 0x2fb5c203U, 0x86c57b9aU, 0xd33708a5U,
	0x302887f2U, 0x23bfa5b2U, 0x02036abaU, 0xed16825cU,
	0x8acf1c2bU, 0xa779b492U, 0xf307f2f0U, 0x4e69e2a1U,
	0x65daf4cdU, 0x0605bed5U, 0xd134621fU, 0xc4a6fe8aU,
	0x342e539dU, 0xa2f355a0U, 0x058ae132U, 0xa4f6eb75U,
	0x0b83ec39U, 0x4060efaaU, 0x5e719f06U, 0xbd6e1051U,
	0x3e218af9U, 0x96dd063dU, 0xdd3e05aeU, 0x4de6bd46U,
	0x91548db5U, 0x71c45d05U, 0x0406d46fU, 0x605015ffU,
	0x1998fb24U, 0xd6bde997U, 0x894043ccU, 0x67d99e77U,
	0xb0e842bdU, 0x07898b88U, 0xe7195b38U, 0x79c8eedbU,
	0xa17c0a47U, 0x7c420fe9U, 0xf8841ec9U, 0x00000000U,
	0x09808683U, 0x322bed48U, 0x1e1170acU, 0x6c5a724eU,
	0xfd0efffbU, 0x0f853856U, 0x3daed51eU, 0x362d3927U,
	0x0a0fd964U, 0x685ca621U, 0x9b5b54d1U, 0x24362e3aU,
	0x0c0a67b1U, 0x9357e70fU, 0xb4ee96d2U, 0x1b9b919eU,
	0x80c0c54fU, 0x61dc20a2U, 0x5a774b69U, 0x1c121a16U,
	0xe293ba0aU, 0xc0a02ae5U, 0x3c22e043U, 0x121b171dU,
	0x0e090d0bU, 0xf28bc7adU, 0x2db6a8b9U, 0x141ea9c8U,
	0x57f11985U, 0xaf75074cU, 0xee99ddbbU, 0xa37f60fdU,
	0xf701269fU, 0x5c72f5bcU, 0x44663bc5U, 0x5bfb7e34U,
	0x8b432976U, 0xcb23c6dcU, 0xb6edfc68U, 0xb8e4f163U,
	0xd731dccaU, 0x42638510U, 0x13972240U, 0x84c61120U,
	0x854a247dU, 0xd2bb3df8U, 0xaef93211U, 0xc729a16dU,
	0x1d9e2f4bU, 0xdcb230f3U, 0x0d8652ecU, 0x77c1e3d0U,
	0x2bb3166cU, 0xa970b999U, 0x119448faU, 0x47e96422U,
	0xa8fc8cc4U, 0xa0f03f1aU, 0x567d2cd8U, 0x223390efU,
	0x87494ec7U, 0xd938d1c1U, 0x8ccaa2feU, 0x98d40b36U,
	0xa6f581cfU, 0xa57ade28U, 0xdab78e26U, 0x3fadbfa4U,
	0x2c3a9de4U, 0x5078920dU, 0x6a5fcc9bU, 0x547e4662U,
	0xf68d13c2U, 0x90d8b8e8U, 0x2e39f75eU, 0x82c3aff5U,
	0x9f5d80beU, 0x69d0937cU, 0x6fd52da9U, 0xcf2512b3U,
	0xc8ac993bU, 0x10187da7U, 0xe89c636eU, 0xdb3bbb7bU,
	0xcd267809U, 0x6e5918f4U, 0xec9ab701U, 0x834f9aa8U,
	0xe6956e65U, 0xaaffe67eU, 0x21bccf08U, 0xef15e8e6U,
	0xbae79bd9U, 0x4a6f36ceU, 0xea9f09d4U, 0x29b07cd6U,
	0x31a4b2afU, 0x2a3f2331U, 0xc6a59430U, 0x35a266c0U,
	0x744ebc37U, 0xfc82caa6U, 0xe090d0b0U, 0x33a7d815U,
	0xf104984aU, 0x41ecdaf7U, 0x7fcd500eU, 0x1791f62fU,
	0x764dd68dU, 0x43efb04dU, 0xccaa4d54U, 0xe49604dfU,
	0x9ed1b5e3U, 0x4c6a881bU, 0xc12c1fb8U, 0x4665517fU,
	0x9d5eea04U, 0x018c355dU, 0xfa877473U, 0xfb0b412eU,
	0xb3671d5aU, 0x92dbd252U, 0xe9105633U, 0x6dd64713U,
	0x9ad7618cU, 0x37a10c7aU, 0x59f8148eU, 0xeb133c89U,
	0xcea927eeU, 0xb761c935U, 0xe11ce5edU, 0x7a47b13cU,
	0x9cd2df59U, 0x55f2733fU, 0x1814ce79U, 0x73c737bfU,
	0x53f7cdeaU, 0x5ffdaa5bU, 0xdf3d6f14U, 0x7844db86U,
	0xcaaff381U, 0xb968c43eU, 0x3824342cU, 0xc2a3405fU,
	0x161dc372U, 0xbce2250cU, 0x283c498bU, 0xff0d9541U,
	0x39a80171U, 0x080cb3deU, 0xd8b4e49cU, 0x6456c190U,
	0x7bcb8461U, 0xd532b670U, 0x486c5c74U, 0xd0b85742U,
};

static const u32 Td1[256] = {
	0x5051f4a7U, 0x537e4165U, 0xc31a17a4U, 0x963a275eU,
	0xcb3bab6bU, 0xf11f9d45U, 0xabacfa58U, 0x934be303U,
	0x552030faU, 0xf6ad766dU, 0x9188cc76U, 0x25f5024cU,
	0xfc4fe5d7U, 0xd7c52acbU, 0x80263544U, 0x8fb562a3U,
	0x49deb15aU, 0x6725ba1bU, 0x9845ea0eU, 0xe15dfec0U,
	0x02c32f75U, 0x12814cf0U, 0xa38d4697U, 0xc66bd3f9U,
	0xe7038f5fU, 0x9515929cU, 0xebbf6d7aU, 0xda955259U,
	0x2dd4be83U, 0xd3587421U, 0x2949e069U, 0x448ec9c8U,
	0x6a75c289U, 0x78f48e79U, 0x6b99583eU, 0xdd27b971U,
	0xb6bee14fU, 0x17f088adU, 0x66c920acU, 0xb47dce3aU,
	0x1863df4aU, 0x82e51a31U, 0x60975133U, 0x4562537fU,
	0xe0b16477U, 0x84bb6baeU, 0x1cfe81a0U, 0x94f9082bU,
	0x58704868U, 0x198f45fdU, 0x8794de6cU, 0xb7527bf8U,
	0x23ab73d3U, 0xe2724b02U, 0x57e31f8fU, 0x2a6655abU,
	0x07b2eb28U, 0x032fb5c2U, 0x9a86c57bU, 0xa5d33708U,
	0xf2302887U, 0xb223bfa5U, 0xba02036aU, 0x5ced1682U,
	0x2b8acf1cU, 0x92a779b4U, 0xf0f307f2U, 0xa14e69e2U,
	0xcd65daf4U, 0xd50605beU, 0x1fd13462U, 0x8ac4a6feU,
	0x9d342e53U, 0xa0a2f355U, 0x32058ae1U, 0x75a4f6ebU,
	0x390b83ecU, 0xaa4060efU, 0x065e719fU, 0x51bd6e10U,
	0xf93e218aU, 0x3d96dd06U, 0xaedd3e05U, 0x464de6bdU,
	0xb591548dU, 0x0571c45dU, 0x6f0406d4U, 0xff605015U,
	0x241998fbU, 0x97d6bde9U, 0xcc894043U, 0x7767d99eU,
	0xbdb0e842U, 0x8807898bU, 0x38e7195bU, 0xdb79c8eeU,
	0x47a17c0aU, 0xe97c420fU, 0xc9f8841eU, 0x00000000U,
	0x83098086U, 0x48322bedU, 0xac1e1170U, 0x4e6c5a72U,
	0xfbfd0effU, 0x560f8538U, 0x1e3daed5U, 0x27362d39U,
	0x640a0fd9U, 0x21685ca6U, 0xd19b5b54U, 0x3a24362eU,
	0xb10c0a67U, 0x0f9357e7U, 0xd2b4ee96U, 0x9e1b9b91U,
	0x4f80c0c5U, 0xa261dc20U, 0x695a774bU, 0x161c121aU,
	0x0ae293baU, 0xe5c0a02aU, 0x433c22e0U, 0x1d121b17U,
	0x0b0e090dU, 0xadf28bc7U, 0xb92db6a8U, 0xc8141ea9U,
	0x8557f119U, 0x4caf7507U, 0xbbee99ddU, 0xfda37f60U,
	0x9ff70126U, 0xbc5c72f5U, 0xc544663bU, 0x345bfb7eU,
	0x768b4329U, 0xdccb23c6U, 0x68b6edfcU, 0x63b8e4f1U,
	0xcad731dcU, 0x10426385U, 0x40139722U, 0x2084c611U,
	0x7d854a24U, 0xf8d2bb3dU, 0x11aef932U, 0x6dc729a1U,
	0x4b1d9e2fU, 0xf3dcb230U, 0xec0d8652U, 0xd077c1e3U,
	0x6c2bb316U, 0x99a970b9U, 0xfa119448U, 0x2247e964U,
	0xc4a8fc8cU, 0x1aa0f03fU, 0xd8567d2cU, 0xef223390U,
	0xc787494eU, 0xc1d938d1U, 0xfe8ccaa2U, 0x3698d40bU,
	0xcfa6f581U, 0x28a57adeU, 0x26dab78eU, 0xa43fadbfU,
	0xe42c3a9dU, 0x0d507892U, 0x9b6a5fccU, 0x62547e46U,
	0xc2f68d13U, 0xe890d8b8U, 0x5e2e39f7U, 0xf582c3afU,
	0xbe9f5d80U, 0x7c69d093U, 0xa96fd52dU, 0xb3cf2512U,
	0x3bc8ac99U, 0xa710187dU, 0x6ee89c63U, 0x7bdb3bbbU,
	0x09cd2678U, 0xf46e5918U, 0x01ec9ab7U, 0xa8834f9aU,
	0x65e6956eU, 0x7eaaffe6U, 0x0821bccfU, 0xe6ef15e8U,
	0xd9bae79bU, 0xce4a6f36U, 0xd4ea9f09U, 0xd629b07cU,
	0xaf31a4b2U, 0x312a3f23U, 0x30c6a594U, 0xc035a266U,
	0x37744ebcU, 0xa6fc82caU, 0xb0e090d0U, 0x1533a7d8U,
	0x4af10498U, 0xf741ecdaU, 0x0e7fcd50U, 0x2f1791f6U,
	0x8d764dd6U, 0x4d43efb0U, 0x54ccaa4dU, 0xdfe49604U,
	0xe39ed1b5U, 0x1b4c6a88U, 0xb8c12c1fU, 0x7f466551U,
	0x049d5eeaU, 0x5d018c35U, 0x73fa8774U, 0x2efb0b41U,
	0x5ab3671dU, 0x5292dbd2U, 0x33e91056U, 0x136dd647U,
	0x8c9ad761U, 0x7a37a10cU, 0x8e59f814U, 0x89eb133cU,
	0xeecea927U, 0x35b761c9U, 0xede11ce5U, 0x3c7a47b1U,
	0x599cd2dfU, 0x3f55f273U, 0x791814ceU, 0xbf73c737U,
	0xea53f7cdU, 0x5b5ffdaaU, 0x14df3d6fU, 0x867844dbU,
	0x81caaff3U, 0x3eb968c4U, 0x2c382434U, 0x5fc2a340U,
	0x72161dc3U, 0x0cbce225U, 0x8b283c49U, 0x41ff0d95U,
	0x7139a801U, 0xde080cb3U, 0x9cd8b4e4U, 0x906456c1U,
	0x617bcb84U, 0x70d532b6U, 0x74486c5cU, 0x42d0b857U,
};
static const u32 Td2[256] = {
	0xa75051f4U, 0x65537e41U, 0xa4c31a17U, 0x5e963a27U,
	0x6bcb3babU, 0x45f11f9dU, 0x58abacfaU, 0x03934be3U,
	0xfa552030U, 0x6df6ad76U, 0x769188ccU, 0x4c25f502U,
	0xd7fc4fe5U, 0xcbd7c52aU, 0x44802635U, 0xa38fb562U,
	0x5a49deb1U, 0x1b6725baU, 0x0e9845eaU, 0xc0e15dfeU,
	0x7502c32fU, 0xf012814cU, 0x97a38d46U, 0xf9c66bd3U,
	0x5fe7038fU, 0x9c951592U, 0x7aebbf6dU, 0x59da9552U,
	0x832dd4beU, 0x21d35874U, 0x692949e0U, 0xc8448ec9U,
	0x896a75c2U, 0x7978f48eU, 0x3e6b9958U, 0x71dd27b9U,
	0x4fb6bee1U, 0xad17f088U, 0xac66c920U, 0x3ab47dceU,
	0x4a1863dfU, 0x3182e51aU, 0x33609751U, 0x7f456253U,
	0x77e0b164U, 0xae84bb6bU, 0xa01cfe81U, 0x2b94f908U,
	0x68587048U, 0xfd198f45U, 0x6c8794deU, 0xf8b7527bU,
	0xd323ab73U, 0x02e2724bU, 0x8f57e31fU, 0xab2a6655U,
	0x2807b2ebU, 0xc2032fb5U, 0x7b9a86c5U, 0x08a5d337U,
	0x87f23028U, 0xa5b223bfU, 0x6aba0203U, 0x825ced16U,
	0x1c2b8acfU, 0xb492a779U, 0xf2f0f307U, 0xe2a14e69U,
	0xf4cd65daU, 0xbed50605U, 0x621fd134U, 0xfe8ac4a6U,
	0x539d342eU, 0x55a0a2f3U, 0xe132058aU, 0xeb75a4f6U,
	0xec390b83U, 0xefaa4060U, 0x9f065e71U, 0x1051bd6eU,
	0x8af93e21U, 0x063d96ddU, 0x05aedd3eU, 0xbd464de6U,
	0x8db59154U, 0x5d0571c4U, 0xd46f0406U, 0x15ff6050U,
	0xfb241998U, 0xe997d6bdU, 0x43cc8940U, 0x9e7767d9U,
	0x42bdb0e8U, 0x8b880789U, 0x5b38e719U, 0xeedb79c8U,
	0x0a47a17cU, 0x0fe97c42U, 0x1ec9f884U, 0x00000000U,
	0x86830980U, 0xed48322bU, 0x70ac1e11U, 0x724e6c5aU,
	0xfffbfd0eU, 0x38560f85U, 0xd51e3daeU, 0x3927362dU,
	0xd9640a0fU, 0xa621685cU, 0x54d19b5bU, 0x2e3a2436U,
	0x67b10c0aU, 0xe70f9357U, 0x96d2b4eeU, 0x919e1b9bU,
	0xc54f80c0U, 0x20a261dcU, 0x4b695a77U, 0x1a161c12U,
	0xba0ae293U, 0x2ae5c0a0U, 0xe0433c22U, 0x171d121bU,
	0x0d0b0e09U, 0xc7adf28bU, 0xa8b92db6U, 0xa9c8141eU,
	0x198557f1U, 0x074caf75U, 0xddbbee99U, 0x60fda37fU,
	0x269ff701U, 0xf5bc5c72U, 0x3bc54466U, 0x7e345bfbU,
	0x29768b43U, 0xc6dccb23U, 0xfc68b6edU, 0xf163b8e4U,
	0xdccad731U, 0x85104263U, 0x22401397U, 0x112084c6U,
	0x247d854aU, 0x3df8d2bbU, 0x3211aef9U, 0xa16dc729U,
	0x2f4b1d9eU, 0x30f3dcb2U, 0x52ec0d86U, 0xe3d077c1U,
	0x166c2bb3U, 0xb999a970U, 0x48fa1194U, 0x642247e9U,
	0x8cc4a8fcU, 0x3f1aa0f0U, 0x2cd8567dU, 0x90ef2233U,
	0x4ec78749U, 0xd1c1d938U, 0xa2fe8ccaU, 0x0b3698d4U,
	0x81cfa6f5U, 0xde28a57aU, 0x8e26dab7U, 0xbfa43fadU,
	0x9de42c3aU, 0x920d5078U, 0xcc9b6a5fU, 0x4662547eU,
	0x13c2f68dU, 0xb8e890d8U, 0xf75e2e39U, 0xaff582c3U,
	0x80be9f5dU, 0x937c69d0U, 0x2da96fd5U, 0x12b3cf25U,
	0x993bc8acU, 0x7da71018U, 0x636ee89cU, 0xbb7bdb3bU,
	0x7809cd26U, 0x18f46e59U, 0xb701ec9aU, 0x9aa8834fU,
	0x6e65e695U, 0xe67eaaffU, 0xcf0821bcU, 0xe8e6ef15U,
	0x9bd9bae7U, 0x36ce4a6fU, 0x09d4ea9fU, 0x7cd629b0U,
	0xb2af31a4U, 0x23312a3fU, 0x9430c6a5U, 0x66c035a2U,
	0xbc37744eU, 0xcaa6fc82U, 0xd0b0e090U, 0xd81533a7U,
	0x984af104U, 0xdaf741ecU, 0x500e7fcdU, 0xf62f1791U,
	0xd68d764dU, 0xb04d43efU, 0x4d54ccaaU, 0x04dfe496U,
	0xb5e39ed1U, 0x881b4c6aU, 0x1fb8c12cU, 0x517f4665U,
	0xea049d5eU, 0x355d018cU, 0x7473fa87U, 0x412efb0bU,
	0x1d5ab367U, 0xd25292dbU, 0x5633e910U, 0x47136dd6U,
	0x618c9ad7U, 0x0c7a37a1U, 0x148e59f8U, 0x3c89eb13U,
	0x27eecea9U, 0xc935b761U, 0xe5ede11cU, 0xb13c7a47U,
	0xdf599cd2U, 0x733f55f2U, 0xce791814U, 0x37bf73c7U,
	0xcdea53f7U, 0xaa5b5ffdU, 0x6f14df3dU, 0xdb867844U,
	0xf381caafU, 0xc43eb968U, 0x342c3824U, 0x405fc2a3U,
	0xc372161dU, 0x250cbce2U, 0x498b283cU, 0x9541ff0dU,
	0x017139a8U, 0xb3de080cU, 0xe49cd8b4U, 0xc1906456U,
	0x84617bcbU, 0xb670d532U, 0x5c74486cU, 0x5742d0b8U,
};
static const u32 Td3[256] = {
	0xf4a75051U, 0x4165537eU, 0x17a4c31aU, 0x275e963aU,
	0xab6bcb3bU, 0x9d45f11fU, 0xfa58abacU, 0xe303934bU,
	0x30fa5520U, 0x766df6adU, 0xcc769188U, 0x024c25f5U,
	0xe5d7fc4fU, 0x2acbd7c5U, 0x35448026U, 0x62a38fb5U,
	0xb15a49deU, 0xba1b6725U, 0xea0e9845U, 0xfec0e15dU,
	0x2f7502c3U, 0x4cf01281U, 0x4697a38dU, 0xd3f9c66bU,
	0x8f5fe703U, 0x929c9515U, 0x6d7aebbfU, 0x5259da95U,
	0xbe832dd4U, 0x7421d358U, 0xe0692949U, 0xc9c8448eU,
	0xc2896a75U, 0x8e7978f4U, 0x583e6b99U, 0xb971dd27U,
	0xe14fb6beU, 0x88ad17f0U, 0x20ac66c9U, 0xce3ab47dU,
	0xdf4a1863U, 0x1a3182e5U, 0x51336097U, 0x537f4562U,
	0x6477e0b1U, 0x6bae84bbU, 0x81a01cfeU, 0x082b94f9U,
	0x48685870U, 0x45fd198fU, 0xde6c8794U, 0x7bf8b752U,
	0x73d323abU, 0x4b02e272U, 0x1f8f57e3U, 0x55ab2a66U,
	0xeb2807b2U, 0xb5c2032fU, 0xc57b9a86U, 0x3708a5d3U,
	0x2887f230U, 0xbfa5b223U, 0x036aba02U, 0x16825cedU,
	0xcf1c2b8aU, 0x79b492a7U, 0x07f2f0f3U, 0x69e2a14eU,
	0xdaf4cd65U, 0x05bed506U, 0x34621fd1U, 0xa6fe8ac4U,
	0x2e539d34U, 0xf355a0a2U, 0x8ae13205U, 0xf6eb75a4U,
	0x83ec390bU, 0x60efaa40U, 0x719f065eU, 0x6e1051bdU,
	0x218af93eU, 0xdd063d96U, 0x3e05aeddU, 0xe6bd464dU,
	0x548db591U, 0xc45d0571U, 0x06d46f04U, 0x5015ff60U,
	0x98fb2419U, 0xbde997d6U, 0x4043cc89U, 0xd99e7767U,
	0xe842bdb0U, 0x898b8807U, 0x195b38e7U, 0xc8eedb79U,
	0x7c0a47a1U, 0x420fe97cU, 0x841ec9f8U, 0x00000000U,
	0x80868309U, 0x2bed4832U, 0x1170ac1eU, 0x5a724e6cU,
	0x0efffbfdU, 0x8538560fU, 0xaed51e3dU, 0x2d392736U,
	0x0fd9640aU, 0x5ca62168U, 0x5b54d19bU, 0x362e3a24U,
	0x0a67b10cU, 0x57e70f93U, 0xee96d2b4U, 0x9b919e1bU,
	0xc0c54f80U, 0xdc20a261U, 0x774b695aU, 0x121a161cU,
	0x93ba0ae2U, 0xa02ae5c0U, 0x22e0433cU, 0x1b171d12U,
	0x090d0b0eU, 0x8bc7adf2U, 0xb6a8b92dU, 0x1ea9c814U,
	0xf1198557U, 0x75074cafU, 0x99ddbbeeU, 0x7f60fda3U,
	0x01269ff7U, 0x72f5bc5cU, 0x663bc544U, 0xfb7e345bU,
	0x4329768bU, 0x23c6dccbU, 0xedfc68b6U, 0xe4f163b8U,
	0x31dccad7U, 0x63851042U, 0x97224013U, 0xc6112084U,
	0x4a247d85U, 0xbb3df8d2U, 0xf93211aeU, 0x29a16dc7U,
	0x9e2f4b1dU, 0xb230f3dcU, 0x8652ec0dU, 0xc1e3d077U,
	0xb3166c2bU, 0x70b999a9U, 0x9448fa11U, 0xe9642247U,
	0xfc8cc4a8U, 0xf03f1aa0U, 0x7d2cd856U, 0x3390ef22U,
	0x494ec787U, 0x38d1c1d9U, 0xcaa2fe8cU, 0xd40b3698U,
	0xf581cfa6U, 0x7ade28a5U, 0xb78e26daU, 0xadbfa43fU,
	0x3a9de42cU, 0x78920d50U, 0x5fcc9b6aU, 0x7e466254U,
	0x8d13c2f6U, 0xd8b8e890U, 0x39f75e2eU, 0xc3aff582U,
	0x5d80be9fU, 0xd0937c69U, 0xd52da96fU, 0x2512b3cfU,
	0xac993bc8U, 0x187da710U, 0x9c636ee8U, 0x3bbb7bdbU,
	0x267809cdU, 0x5918f46eU, 0x9ab701ecU, 0x4f9aa883U,
	0x956e65e6U, 0xffe67eaaU, 0xbccf0821U, 0x15e8e6efU,
	0xe79bd9baU, 0x6f36ce4aU, 0x9f09d4eaU, 0xb07cd629U,
	0xa4b2af31U, 0x3f23312aU, 0xa59430c6U, 0xa266c035U,
	0x4ebc3774U, 0x82caa6fcU, 0x90d0b0e0U, 0xa7d81533U,
	0x04984af1U, 0xecdaf741U, 0xcd500e7fU, 0x91f62f17U,
	0x4dd68d76U, 0xefb04d43U, 0xaa4d54ccU, 0x9604dfe4U,
	0xd1b5e39eU, 0x6a881b4cU, 0x2c1fb8c1U, 0x65517f46U,
	0x5eea049dU, 0x8c355d01U, 0x877473faU, 0x0b412efbU,
	0x671d5ab3U, 0xdbd25292U, 0x105633e9U, 0xd647136dU,
	0xd7618c9aU, 0xa10c7a37U, 0xf8148e59U, 0x133c89ebU,
	0xa927eeceU, 0x61c935b7U, 0x1ce5ede1U, 0x47b13c7aU,
	0xd2df599cU, 0xf2733f55U, 0x14ce7918U, 0xc737bf73U,
	0xf7cdea53U, 0xfdaa5b5fU, 0x3d6f14dfU, 0x44db8678U,
	0xaff381caU, 0x68c43eb9U, 0x24342c38U, 0xa3405fc2U,
	0x1dc37216U, 0xe2250cbcU, 0x3c498b28U, 0x0d9541ffU,
	0xa8017139U, 0x0cb3de08U, 0xb4e49cd8U, 0x56c19064U,
	0xcb84617bU, 0x32b670d5U, 0x6c5c7448U, 0xb85742d0U,
};
static const u8 Td4[256] = {
	0x52U, 0x09U, 0x6aU, 0xd5U, 0x30U, 0x36U, 0xa5U, 0x38U,
	0xbfU, 0x40U, 0xa3U, 0x9eU, 0x81U, 0xf3U, 0xd7U, 0xfbU,
	0x7cU, 0xe3U, 0x39U, 0x82U, 0x9bU, 0x2fU, 0xffU, 0x87U,
	0x34U, 0x8eU, 0x43U, 0x44U, 0xc4U, 0xdeU, 0xe9U, 0xcbU,
	0x54U, 0x7bU, 0x94U, 0x32U, 0xa6U, 0xc2U, 0x23U, 0x3dU,
	0xeeU, 0x4cU, 0x95U, 0x0bU, 0x42U, 0xfaU, 0xc3U, 0x4eU,
	0x08U, 0x2eU, 0xa1U, 0x66U, 0x28U, 0xd9U, 0x24U, 0xb2U,
	0x76U, 0x5bU, 0xa2U, 0x49U, 0x6dU, 0x8bU, 0xd1U, 0x25U,
	0x72U, 0xf8U, 0xf6U, 0x64U, 0x86U, 0x68U, 0x98U, 0x16U,
	0xd4U, 0xa4U, 0x5cU, 0xccU, 0x5dU, 0x65U, 0xb6U, 0x92U,
	0x6cU, 0x70U, 0x48U, 0x50U, 0xfdU, 0xedU, 0xb9U, 0xdaU,
	0x5eU, 0x15U, 0x46U, 0x57U, 0xa7U, 0x8dU, 0x9dU, 0x84U,
	0x90U, 0xd8U, 0xabU, 0x00U, 0x8cU, 0xbcU, 0xd3U, 0x0aU,
	0xf7U, 0xe4U, 0x58U, 0x05U, 0xb8U, 0xb3U, 0x45U, 0x06U,
	0xd0U, 0x2cU, 0x1eU, 0x8fU, 0xcaU, 0x3fU, 0x0fU, 0x02U,
	0xc1U, 0xafU, 0xbdU, 0x03U, 0x01U, 0x13U, 0x8aU, 0x6bU,
	0x3aU, 0x91U, 0x11U, 0x41U, 0x4fU, 0x67U, 0xdcU, 0xeaU,
	0x97U, 0xf2U, 0xcfU, 0xceU, 0xf0U, 0xb4U, 0xe6U, 0x73U,
	0x96U, 0xacU, 0x74U, 0x22U, 0xe7U, 0xadU, 0x35U, 0x85U,
	0xe2U, 0xf9U, 0x37U, 0xe8U, 0x1cU, 0x75U, 0xdfU, 0x6eU,
	0x47U, 0xf1U, 0x1aU, 0x71U, 0x1dU, 0x29U, 0xc5U, 0x89U,
	0x6fU, 0xb7U, 0x62U, 0x0eU, 0xaaU, 0x18U, 0xbeU, 0x1bU,
	0xfcU, 0x56U, 0x3eU, 0x4bU, 0xc6U, 0xd2U, 0x79U, 0x20U,
	0x9aU, 0xdbU, 0xc0U, 0xfeU, 0x78U, 0xcdU, 0x5aU, 0xf4U,
	0x1fU, 0xddU, 0xa8U, 0x33U, 0x88U, 0x07U, 0xc7U, 0x31U,
	0xb1U, 0x12U, 0x10U, 0x59U, 0x27U, 0x80U, 0xecU, 0x5fU,
	0x60U, 0x51U, 0x7fU, 0xa9U, 0x19U, 0xb5U, 0x4aU, 0x0dU,
	0x2dU, 0xe5U, 0x7aU, 0x9fU, 0x93U, 0xc9U, 0x9cU, 0xefU,
	0xa0U, 0xe0U, 0x3bU, 0x4dU, 0xaeU, 0x2aU, 0xf5U, 0xb0U,
	0xc8U, 0xebU, 0xbbU, 0x3cU, 0x83U, 0x53U, 0x99U, 0x61U,
	0x17U, 0x2bU, 0x04U, 0x7eU, 0xbaU, 0x77U, 0xd6U, 0x26U,
	0xe1U, 0x69U, 0x14U, 0x63U, 0x55U, 0x21U, 0x0cU, 0x7dU,
};
static const u32 rcon[] = {
	0x01000000, 0x02000000, 0x04000000, 0x08000000,
	0x10000000, 0x20000000, 0x40000000, 0x80000000,
	0x1B000000, 0x36000000, /* for 128-bit blocks, Rijndael never uses more than 10 rcon values */
};



# if defined(_MSC_VER) && (defined(_M_IX86) || defined(_M_AMD64) || defined(_M_X64))
#  define SWAP(x) (_lrotl(x, 8) & 0x00ff00ff | _lrotr(x, 8) & 0xff00ff00)
#  define GETU32(p) SWAP(*((u32 *)(p)))
#  define PUTU32(ct, st) { *((u32 *)(ct)) = SWAP((st)); }
# else
#  define GETU32(pt) (((u32)(pt)[0] << 24) ^ ((u32)(pt)[1] << 16) ^ ((u32)(pt)[2] <<  8) ^ ((u32)(pt)[3]))
#  define PUTU32(ct, st) { (ct)[0] = (u8)((st) >> 24); (ct)[1] = (u8)((st) >> 16); (ct)[2] = (u8)((st) >>  8); (ct)[3] = (u8)(st); }
# endif

void AES_cbc_encrypt(const unsigned char *in, unsigned char *out,
	size_t len, const AES_KEY *key,
	unsigned char *ivec);
int private_AES_set_encrypt_key(const unsigned char *userKey, const int bits,
	AES_KEY *key);
int private_AES_set_encrypt_key(const unsigned char *userKey, const int bits,
	AES_KEY *key)
{

	u32 *rk;
	int i = 0;
	u32 temp;

	if (!userKey || !key)
		return -1;
	if (bits != 128 && bits != 192 && bits != 256)
		return -2;

	rk = key->rd_key;

	if (bits == 128)
		key->rounds = 10;
	else if (bits == 192)
		key->rounds = 12;
	else
		key->rounds = 14;

	rk[0] = GETU32(userKey);
	rk[1] = GETU32(userKey + 4);
	rk[2] = GETU32(userKey + 8);
	rk[3] = GETU32(userKey + 12);
	if (bits == 128) {
		while (1) {
			temp = rk[3];
			rk[4] = rk[0] ^
				(Te2[(temp >> 16) & 0xff] & 0xff000000) ^
				(Te3[(temp >> 8) & 0xff] & 0x00ff0000) ^
				(Te0[(temp)& 0xff] & 0x0000ff00) ^
				(Te1[(temp >> 24)] & 0x000000ff) ^
				rcon[i];
			rk[5] = rk[1] ^ rk[4];
			rk[6] = rk[2] ^ rk[5];
			rk[7] = rk[3] ^ rk[6];
			if (++i == 10) {
				return 0;
			}
			rk += 4;
		}
	}
	rk[4] = GETU32(userKey + 16);
	rk[5] = GETU32(userKey + 20);
	if (bits == 192) {
		while (1) {
			temp = rk[5];
			rk[6] = rk[0] ^
				(Te2[(temp >> 16) & 0xff] & 0xff000000) ^
				(Te3[(temp >> 8) & 0xff] & 0x00ff0000) ^
				(Te0[(temp)& 0xff] & 0x0000ff00) ^
				(Te1[(temp >> 24)] & 0x000000ff) ^
				rcon[i];
			rk[7] = rk[1] ^ rk[6];
			rk[8] = rk[2] ^ rk[7];
			rk[9] = rk[3] ^ rk[8];
			if (++i == 8) {
				return 0;
			}
			rk[10] = rk[4] ^ rk[9];
			rk[11] = rk[5] ^ rk[10];
			rk += 6;
		}
	}
	rk[6] = GETU32(userKey + 24);
	rk[7] = GETU32(userKey + 28);
	if (bits == 256) {
		while (1) {
			temp = rk[7];
			rk[8] = rk[0] ^
				(Te2[(temp >> 16) & 0xff] & 0xff000000) ^
				(Te3[(temp >> 8) & 0xff] & 0x00ff0000) ^
				(Te0[(temp)& 0xff] & 0x0000ff00) ^
				(Te1[(temp >> 24)] & 0x000000ff) ^
				rcon[i];
			rk[9] = rk[1] ^ rk[8];
			rk[10] = rk[2] ^ rk[9];
			rk[11] = rk[3] ^ rk[10];
			if (++i == 7) {
				return 0;
			}
			temp = rk[11];
			rk[12] = rk[4] ^
				(Te2[(temp >> 24)] & 0xff000000) ^
				(Te3[(temp >> 16) & 0xff] & 0x00ff0000) ^
				(Te0[(temp >> 8) & 0xff] & 0x0000ff00) ^
				(Te1[(temp)& 0xff] & 0x000000ff);
			rk[13] = rk[5] ^ rk[12];
			rk[14] = rk[6] ^ rk[13];
			rk[15] = rk[7] ^ rk[14];

			rk += 8;
		}
	}
	return 0;
}


void AES_encrypt(const unsigned char *in, unsigned char *out,
	const AES_KEY *key);

void CRYPTO_cbc128_encrypt(const unsigned char *in, unsigned char *out,
	size_t len, const void *key,
	unsigned char ivec[16], block128_f block)
{
	size_t n;
	const unsigned char *iv = ivec;

	assert(in && out && key && ivec);

#if !defined(OPENSSL_SMALL_FOOTPRINT)
	if (STRICT_ALIGNMENT &&
		((size_t)in | (size_t)out | (size_t)ivec) % sizeof(size_t) != 0) {
		while (len >= 16) {
			for (n = 0; n < 16; ++n)
				out[n] = in[n] ^ iv[n];
			(*block) (out, out, key);
			iv = out;
			len -= 16;
			in += 16;
			out += 16;
		}
	}
	else {
		while (len >= 16) {
			for (n = 0; n < 16; n += sizeof(size_t))
				*(size_t *)(out + n) =
				*(size_t *)(in + n) ^ *(size_t *)(iv + n);
			(*block) (out, out, key);
			iv = out;
			len -= 16;
			in += 16;
			out += 16;
		}
	}
#endif
	while (len) {
		for (n = 0; n < 16 && n < len; ++n)
			out[n] = in[n] ^ iv[n];
		for (; n < 16; ++n)
			out[n] = iv[n];
		(*block) (out, out, key);
		//AES_encrypt(out, out,(const AES_KEY*) key);
		iv = out;
		if (len <= 16)
			break;
		len -= 16;
		in += 16;
		out += 16;
	}
	memcpy(ivec, iv, 16);
}




void AES_encrypt(const unsigned char *in, unsigned char *out,
	const AES_KEY *key){
	const u32 *rk;
	u32 s0, s1, s2, s3, t0, t1, t2, t3;
#ifndef FULL_UNROLL
	int r;
#endif /* ?FULL_UNROLL */

	assert(in && out && key);
	rk = key->rd_key;

	/*
	* map byte array block to cipher state
	* and add initial round key:
	*/
	s0 = GETU32(in) ^ rk[0];
	s1 = GETU32(in + 4) ^ rk[1];
	s2 = GETU32(in + 8) ^ rk[2];
	s3 = GETU32(in + 12) ^ rk[3];
#ifdef FULL_UNROLL
	/* round 1: */
	t0 = Te0[s0 >> 24] ^ Te1[(s1 >> 16) & 0xff] ^ Te2[(s2 >> 8) & 0xff] ^ Te3[s3 & 0xff] ^ rk[4];
	t1 = Te0[s1 >> 24] ^ Te1[(s2 >> 16) & 0xff] ^ Te2[(s3 >> 8) & 0xff] ^ Te3[s0 & 0xff] ^ rk[5];
	t2 = Te0[s2 >> 24] ^ Te1[(s3 >> 16) & 0xff] ^ Te2[(s0 >> 8) & 0xff] ^ Te3[s1 & 0xff] ^ rk[6];
	t3 = Te0[s3 >> 24] ^ Te1[(s0 >> 16) & 0xff] ^ Te2[(s1 >> 8) & 0xff] ^ Te3[s2 & 0xff] ^ rk[7];
	/* round 2: */
	s0 = Te0[t0 >> 24] ^ Te1[(t1 >> 16) & 0xff] ^ Te2[(t2 >> 8) & 0xff] ^ Te3[t3 & 0xff] ^ rk[8];
	s1 = Te0[t1 >> 24] ^ Te1[(t2 >> 16) & 0xff] ^ Te2[(t3 >> 8) & 0xff] ^ Te3[t0 & 0xff] ^ rk[9];
	s2 = Te0[t2 >> 24] ^ Te1[(t3 >> 16) & 0xff] ^ Te2[(t0 >> 8) & 0xff] ^ Te3[t1 & 0xff] ^ rk[10];
	s3 = Te0[t3 >> 24] ^ Te1[(t0 >> 16) & 0xff] ^ Te2[(t1 >> 8) & 0xff] ^ Te3[t2 & 0xff] ^ rk[11];
	/* round 3: */
	t0 = Te0[s0 >> 24] ^ Te1[(s1 >> 16) & 0xff] ^ Te2[(s2 >> 8) & 0xff] ^ Te3[s3 & 0xff] ^ rk[12];
	t1 = Te0[s1 >> 24] ^ Te1[(s2 >> 16) & 0xff] ^ Te2[(s3 >> 8) & 0xff] ^ Te3[s0 & 0xff] ^ rk[13];
	t2 = Te0[s2 >> 24] ^ Te1[(s3 >> 16) & 0xff] ^ Te2[(s0 >> 8) & 0xff] ^ Te3[s1 & 0xff] ^ rk[14];
	t3 = Te0[s3 >> 24] ^ Te1[(s0 >> 16) & 0xff] ^ Te2[(s1 >> 8) & 0xff] ^ Te3[s2 & 0xff] ^ rk[15];
	/* round 4: */
	s0 = Te0[t0 >> 24] ^ Te1[(t1 >> 16) & 0xff] ^ Te2[(t2 >> 8) & 0xff] ^ Te3[t3 & 0xff] ^ rk[16];
	s1 = Te0[t1 >> 24] ^ Te1[(t2 >> 16) & 0xff] ^ Te2[(t3 >> 8) & 0xff] ^ Te3[t0 & 0xff] ^ rk[17];
	s2 = Te0[t2 >> 24] ^ Te1[(t3 >> 16) & 0xff] ^ Te2[(t0 >> 8) & 0xff] ^ Te3[t1 & 0xff] ^ rk[18];
	s3 = Te0[t3 >> 24] ^ Te1[(t0 >> 16) & 0xff] ^ Te2[(t1 >> 8) & 0xff] ^ Te3[t2 & 0xff] ^ rk[19];
	/* round 5: */
	t0 = Te0[s0 >> 24] ^ Te1[(s1 >> 16) & 0xff] ^ Te2[(s2 >> 8) & 0xff] ^ Te3[s3 & 0xff] ^ rk[20];
	t1 = Te0[s1 >> 24] ^ Te1[(s2 >> 16) & 0xff] ^ Te2[(s3 >> 8) & 0xff] ^ Te3[s0 & 0xff] ^ rk[21];
	t2 = Te0[s2 >> 24] ^ Te1[(s3 >> 16) & 0xff] ^ Te2[(s0 >> 8) & 0xff] ^ Te3[s1 & 0xff] ^ rk[22];
	t3 = Te0[s3 >> 24] ^ Te1[(s0 >> 16) & 0xff] ^ Te2[(s1 >> 8) & 0xff] ^ Te3[s2 & 0xff] ^ rk[23];
	/* round 6: */
	s0 = Te0[t0 >> 24] ^ Te1[(t1 >> 16) & 0xff] ^ Te2[(t2 >> 8) & 0xff] ^ Te3[t3 & 0xff] ^ rk[24];
	s1 = Te0[t1 >> 24] ^ Te1[(t2 >> 16) & 0xff] ^ Te2[(t3 >> 8) & 0xff] ^ Te3[t0 & 0xff] ^ rk[25];
	s2 = Te0[t2 >> 24] ^ Te1[(t3 >> 16) & 0xff] ^ Te2[(t0 >> 8) & 0xff] ^ Te3[t1 & 0xff] ^ rk[26];
	s3 = Te0[t3 >> 24] ^ Te1[(t0 >> 16) & 0xff] ^ Te2[(t1 >> 8) & 0xff] ^ Te3[t2 & 0xff] ^ rk[27];
	/* round 7: */
	t0 = Te0[s0 >> 24] ^ Te1[(s1 >> 16) & 0xff] ^ Te2[(s2 >> 8) & 0xff] ^ Te3[s3 & 0xff] ^ rk[28];
	t1 = Te0[s1 >> 24] ^ Te1[(s2 >> 16) & 0xff] ^ Te2[(s3 >> 8) & 0xff] ^ Te3[s0 & 0xff] ^ rk[29];
	t2 = Te0[s2 >> 24] ^ Te1[(s3 >> 16) & 0xff] ^ Te2[(s0 >> 8) & 0xff] ^ Te3[s1 & 0xff] ^ rk[30];
	t3 = Te0[s3 >> 24] ^ Te1[(s0 >> 16) & 0xff] ^ Te2[(s1 >> 8) & 0xff] ^ Te3[s2 & 0xff] ^ rk[31];
	/* round 8: */
	s0 = Te0[t0 >> 24] ^ Te1[(t1 >> 16) & 0xff] ^ Te2[(t2 >> 8) & 0xff] ^ Te3[t3 & 0xff] ^ rk[32];
	s1 = Te0[t1 >> 24] ^ Te1[(t2 >> 16) & 0xff] ^ Te2[(t3 >> 8) & 0xff] ^ Te3[t0 & 0xff] ^ rk[33];
	s2 = Te0[t2 >> 24] ^ Te1[(t3 >> 16) & 0xff] ^ Te2[(t0 >> 8) & 0xff] ^ Te3[t1 & 0xff] ^ rk[34];
	s3 = Te0[t3 >> 24] ^ Te1[(t0 >> 16) & 0xff] ^ Te2[(t1 >> 8) & 0xff] ^ Te3[t2 & 0xff] ^ rk[35];
	/* round 9: */
	t0 = Te0[s0 >> 24] ^ Te1[(s1 >> 16) & 0xff] ^ Te2[(s2 >> 8) & 0xff] ^ Te3[s3 & 0xff] ^ rk[36];
	t1 = Te0[s1 >> 24] ^ Te1[(s2 >> 16) & 0xff] ^ Te2[(s3 >> 8) & 0xff] ^ Te3[s0 & 0xff] ^ rk[37];
	t2 = Te0[s2 >> 24] ^ Te1[(s3 >> 16) & 0xff] ^ Te2[(s0 >> 8) & 0xff] ^ Te3[s1 & 0xff] ^ rk[38];
	t3 = Te0[s3 >> 24] ^ Te1[(s0 >> 16) & 0xff] ^ Te2[(s1 >> 8) & 0xff] ^ Te3[s2 & 0xff] ^ rk[39];
	if (key->rounds > 10) {
		/* round 10: */
		s0 = Te0[t0 >> 24] ^ Te1[(t1 >> 16) & 0xff] ^ Te2[(t2 >> 8) & 0xff] ^ Te3[t3 & 0xff] ^ rk[40];
		s1 = Te0[t1 >> 24] ^ Te1[(t2 >> 16) & 0xff] ^ Te2[(t3 >> 8) & 0xff] ^ Te3[t0 & 0xff] ^ rk[41];
		s2 = Te0[t2 >> 24] ^ Te1[(t3 >> 16) & 0xff] ^ Te2[(t0 >> 8) & 0xff] ^ Te3[t1 & 0xff] ^ rk[42];
		s3 = Te0[t3 >> 24] ^ Te1[(t0 >> 16) & 0xff] ^ Te2[(t1 >> 8) & 0xff] ^ Te3[t2 & 0xff] ^ rk[43];
		/* round 11: */
		t0 = Te0[s0 >> 24] ^ Te1[(s1 >> 16) & 0xff] ^ Te2[(s2 >> 8) & 0xff] ^ Te3[s3 & 0xff] ^ rk[44];
		t1 = Te0[s1 >> 24] ^ Te1[(s2 >> 16) & 0xff] ^ Te2[(s3 >> 8) & 0xff] ^ Te3[s0 & 0xff] ^ rk[45];
		t2 = Te0[s2 >> 24] ^ Te1[(s3 >> 16) & 0xff] ^ Te2[(s0 >> 8) & 0xff] ^ Te3[s1 & 0xff] ^ rk[46];
		t3 = Te0[s3 >> 24] ^ Te1[(s0 >> 16) & 0xff] ^ Te2[(s1 >> 8) & 0xff] ^ Te3[s2 & 0xff] ^ rk[47];
		if (key->rounds > 12) {
			/* round 12: */
			s0 = Te0[t0 >> 24] ^ Te1[(t1 >> 16) & 0xff] ^ Te2[(t2 >> 8) & 0xff] ^ Te3[t3 & 0xff] ^ rk[48];
			s1 = Te0[t1 >> 24] ^ Te1[(t2 >> 16) & 0xff] ^ Te2[(t3 >> 8) & 0xff] ^ Te3[t0 & 0xff] ^ rk[49];
			s2 = Te0[t2 >> 24] ^ Te1[(t3 >> 16) & 0xff] ^ Te2[(t0 >> 8) & 0xff] ^ Te3[t1 & 0xff] ^ rk[50];
			s3 = Te0[t3 >> 24] ^ Te1[(t0 >> 16) & 0xff] ^ Te2[(t1 >> 8) & 0xff] ^ Te3[t2 & 0xff] ^ rk[51];
			/* round 13: */
			t0 = Te0[s0 >> 24] ^ Te1[(s1 >> 16) & 0xff] ^ Te2[(s2 >> 8) & 0xff] ^ Te3[s3 & 0xff] ^ rk[52];
			t1 = Te0[s1 >> 24] ^ Te1[(s2 >> 16) & 0xff] ^ Te2[(s3 >> 8) & 0xff] ^ Te3[s0 & 0xff] ^ rk[53];
			t2 = Te0[s2 >> 24] ^ Te1[(s3 >> 16) & 0xff] ^ Te2[(s0 >> 8) & 0xff] ^ Te3[s1 & 0xff] ^ rk[54];
			t3 = Te0[s3 >> 24] ^ Te1[(s0 >> 16) & 0xff] ^ Te2[(s1 >> 8) & 0xff] ^ Te3[s2 & 0xff] ^ rk[55];
		}
	}
	rk += key->rounds << 2;
#else  /* !FULL_UNROLL */
	/*
	* Nr - 1 full rounds:
	*/
	r = key->rounds >> 1;
	for (;;) {
		t0 =
			Te0[(s0 >> 24)] ^
			Te1[(s1 >> 16) & 0xff] ^
			Te2[(s2 >> 8) & 0xff] ^
			Te3[(s3)& 0xff] ^
			rk[4];
		t1 =
			Te0[(s1 >> 24)] ^
			Te1[(s2 >> 16) & 0xff] ^
			Te2[(s3 >> 8) & 0xff] ^
			Te3[(s0)& 0xff] ^
			rk[5];
		t2 =
			Te0[(s2 >> 24)] ^
			Te1[(s3 >> 16) & 0xff] ^
			Te2[(s0 >> 8) & 0xff] ^
			Te3[(s1)& 0xff] ^
			rk[6];
		t3 =
			Te0[(s3 >> 24)] ^
			Te1[(s0 >> 16) & 0xff] ^
			Te2[(s1 >> 8) & 0xff] ^
			Te3[(s2)& 0xff] ^
			rk[7];

		rk += 8;
		if (--r == 0) {
			break;
		}

		s0 =
			Te0[(t0 >> 24)] ^
			Te1[(t1 >> 16) & 0xff] ^
			Te2[(t2 >> 8) & 0xff] ^
			Te3[(t3)& 0xff] ^
			rk[0];
		s1 =
			Te0[(t1 >> 24)] ^
			Te1[(t2 >> 16) & 0xff] ^
			Te2[(t3 >> 8) & 0xff] ^
			Te3[(t0)& 0xff] ^
			rk[1];
		s2 =
			Te0[(t2 >> 24)] ^
			Te1[(t3 >> 16) & 0xff] ^
			Te2[(t0 >> 8) & 0xff] ^
			Te3[(t1)& 0xff] ^
			rk[2];
		s3 =
			Te0[(t3 >> 24)] ^
			Te1[(t0 >> 16) & 0xff] ^
			Te2[(t1 >> 8) & 0xff] ^
			Te3[(t2)& 0xff] ^
			rk[3];
	}
#endif /* ?FULL_UNROLL */
	/*
	* apply last round and
	* map cipher state to byte array block:
	*/
	s0 =
		(Te2[(t0 >> 24)] & 0xff000000) ^
		(Te3[(t1 >> 16) & 0xff] & 0x00ff0000) ^
		(Te0[(t2 >> 8) & 0xff] & 0x0000ff00) ^
		(Te1[(t3)& 0xff] & 0x000000ff) ^
		rk[0];
	PUTU32(out, s0);
	s1 =
		(Te2[(t1 >> 24)] & 0xff000000) ^
		(Te3[(t2 >> 16) & 0xff] & 0x00ff0000) ^
		(Te0[(t3 >> 8) & 0xff] & 0x0000ff00) ^
		(Te1[(t0)& 0xff] & 0x000000ff) ^
		rk[1];
	PUTU32(out + 4, s1);
	s2 =
		(Te2[(t2 >> 24)] & 0xff000000) ^
		(Te3[(t3 >> 16) & 0xff] & 0x00ff0000) ^
		(Te0[(t0 >> 8) & 0xff] & 0x0000ff00) ^
		(Te1[(t1)& 0xff] & 0x000000ff) ^
		rk[2];
	PUTU32(out + 8, s2);
	s3 =
		(Te2[(t3 >> 24)] & 0xff000000) ^
		(Te3[(t0 >> 16) & 0xff] & 0x00ff0000) ^
		(Te0[(t1 >> 8) & 0xff] & 0x0000ff00) ^
		(Te1[(t2)& 0xff] & 0x000000ff) ^
		rk[3];
	PUTU32(out + 12, s3);

}

void AES_cbc_encrypt(const unsigned char *in, unsigned char *out,
	size_t len, const AES_KEY *key,
	unsigned char *ivec)
{
	CRYPTO_cbc128_encrypt(in, out, len, key, ivec,
		(block128_f)AES_encrypt);
}


/**
* Expand the cipher key into the decryption key schedule.
*/
int private_AES_set_decrypt_key(const unsigned char *userKey, const int bits,
	AES_KEY *key)
{

	u32 *rk;
	int i, j, status;
	u32 temp;

	/* first, start with an encryption schedule */
	status = private_AES_set_encrypt_key(userKey, bits, key);
	if (status < 0)
		return status;

	rk = key->rd_key;

	/* invert the order of the round keys: */
	for (i = 0, j = 4 * (key->rounds); i < j; i += 4, j -= 4) {
		temp = rk[i]; rk[i] = rk[j]; rk[j] = temp;
		temp = rk[i + 1]; rk[i + 1] = rk[j + 1]; rk[j + 1] = temp;
		temp = rk[i + 2]; rk[i + 2] = rk[j + 2]; rk[j + 2] = temp;
		temp = rk[i + 3]; rk[i + 3] = rk[j + 3]; rk[j + 3] = temp;
	}
	/* apply the inverse MixColumn transform to all round keys but the first and the last: */
	for (i = 1; i < (key->rounds); i++) {
		rk += 4;
		rk[0] =
			Td0[Te1[(rk[0] >> 24)] & 0xff] ^
			Td1[Te1[(rk[0] >> 16) & 0xff] & 0xff] ^
			Td2[Te1[(rk[0] >> 8) & 0xff] & 0xff] ^
			Td3[Te1[(rk[0]) & 0xff] & 0xff];
		rk[1] =
			Td0[Te1[(rk[1] >> 24)] & 0xff] ^
			Td1[Te1[(rk[1] >> 16) & 0xff] & 0xff] ^
			Td2[Te1[(rk[1] >> 8) & 0xff] & 0xff] ^
			Td3[Te1[(rk[1]) & 0xff] & 0xff];
		rk[2] =
			Td0[Te1[(rk[2] >> 24)] & 0xff] ^
			Td1[Te1[(rk[2] >> 16) & 0xff] & 0xff] ^
			Td2[Te1[(rk[2] >> 8) & 0xff] & 0xff] ^
			Td3[Te1[(rk[2]) & 0xff] & 0xff];
		rk[3] =
			Td0[Te1[(rk[3] >> 24)] & 0xff] ^
			Td1[Te1[(rk[3] >> 16) & 0xff] & 0xff] ^
			Td2[Te1[(rk[3] >> 8) & 0xff] & 0xff] ^
			Td3[Te1[(rk[3]) & 0xff] & 0xff];
	}
	return 0;
}


void CRYPTO_cbc128_decrypt(const unsigned char *in, unsigned char *out,
	size_t len, const void *key,
	unsigned char ivec[16], block128_f block)
{
	size_t n;
	union {
		size_t t[16 / sizeof(size_t)];
		unsigned char c[16];
	} tmp;

	assert(in && out && key && ivec);

#if !defined(OPENSSL_SMALL_FOOTPRINT)
	if (in != out) {
		const unsigned char *iv = ivec;

		if (STRICT_ALIGNMENT &&
			((size_t)in | (size_t)out | (size_t)ivec) % sizeof(size_t) != 0) {
			while (len >= 16) {
				(*block) (in, out, key);
				for (n = 0; n < 16; ++n)
					out[n] ^= iv[n];
				iv = in;
				len -= 16;
				in += 16;
				out += 16;
			}
		}
		else if (16 % sizeof(size_t) == 0) { /* always true */
			while (len >= 16) {
				size_t *out_t = (size_t *)out, *iv_t = (size_t *)iv;

				(*block) (in, out, key);
				for (n = 0; n < 16 / sizeof(size_t); n++)
					out_t[n] ^= iv_t[n];
				iv = in;
				len -= 16;
				in += 16;
				out += 16;
			}
		}
		memcpy(ivec, iv, 16);
	}
	else {
		if (STRICT_ALIGNMENT &&
			((size_t)in | (size_t)out | (size_t)ivec) % sizeof(size_t) != 0) {
			unsigned char c;
			while (len >= 16) {
				(*block) (in, tmp.c, key);
				for (n = 0; n < 16; ++n) {
					c = in[n];
					out[n] = tmp.c[n] ^ ivec[n];
					ivec[n] = c;
				}
				len -= 16;
				in += 16;
				out += 16;
			}
		}
		else if (16 % sizeof(size_t) == 0) { /* always true */
			while (len >= 16) {
				size_t c, *out_t = (size_t *)out, *ivec_t = (size_t *)ivec;
				const size_t *in_t = (const size_t *)in;

				(*block) (in, tmp.c, key);
				for (n = 0; n < 16 / sizeof(size_t); n++) {
					c = in_t[n];
					out_t[n] = tmp.t[n] ^ ivec_t[n];
					ivec_t[n] = c;
				}
				len -= 16;
				in += 16;
				out += 16;
			}
		}
	}
#endif
	while (len) {
		unsigned char c;
		(*block) (in, tmp.c, key);
		for (n = 0; n < 16 && n < len; ++n) {
			c = in[n];
			out[n] = tmp.c[n] ^ ivec[n];
			ivec[n] = c;
		}
		if (len <= 16) {
			for (; n < 16; ++n)
				ivec[n] = in[n];
			break;
		}
		len -= 16;
		in += 16;
		out += 16;
	}
}


/*
* Decrypt a single block
* in and out can overlap
*/
void AES_decrypt(const unsigned char *in, unsigned char *out,
	const AES_KEY *key)
{

	const u32 *rk;
	u32 s0, s1, s2, s3, t0, t1, t2, t3;
#ifndef FULL_UNROLL
	int r;
#endif /* ?FULL_UNROLL */

	assert(in && out && key);
	rk = key->rd_key;

	/*
	* map byte array block to cipher state
	* and add initial round key:
	*/
	s0 = GETU32(in) ^ rk[0];
	s1 = GETU32(in + 4) ^ rk[1];
	s2 = GETU32(in + 8) ^ rk[2];
	s3 = GETU32(in + 12) ^ rk[3];
#ifdef FULL_UNROLL
	/* round 1: */
	t0 = Td0[s0 >> 24] ^ Td1[(s3 >> 16) & 0xff] ^ Td2[(s2 >> 8) & 0xff] ^ Td3[s1 & 0xff] ^ rk[4];
	t1 = Td0[s1 >> 24] ^ Td1[(s0 >> 16) & 0xff] ^ Td2[(s3 >> 8) & 0xff] ^ Td3[s2 & 0xff] ^ rk[5];
	t2 = Td0[s2 >> 24] ^ Td1[(s1 >> 16) & 0xff] ^ Td2[(s0 >> 8) & 0xff] ^ Td3[s3 & 0xff] ^ rk[6];
	t3 = Td0[s3 >> 24] ^ Td1[(s2 >> 16) & 0xff] ^ Td2[(s1 >> 8) & 0xff] ^ Td3[s0 & 0xff] ^ rk[7];
	/* round 2: */
	s0 = Td0[t0 >> 24] ^ Td1[(t3 >> 16) & 0xff] ^ Td2[(t2 >> 8) & 0xff] ^ Td3[t1 & 0xff] ^ rk[8];
	s1 = Td0[t1 >> 24] ^ Td1[(t0 >> 16) & 0xff] ^ Td2[(t3 >> 8) & 0xff] ^ Td3[t2 & 0xff] ^ rk[9];
	s2 = Td0[t2 >> 24] ^ Td1[(t1 >> 16) & 0xff] ^ Td2[(t0 >> 8) & 0xff] ^ Td3[t3 & 0xff] ^ rk[10];
	s3 = Td0[t3 >> 24] ^ Td1[(t2 >> 16) & 0xff] ^ Td2[(t1 >> 8) & 0xff] ^ Td3[t0 & 0xff] ^ rk[11];
	/* round 3: */
	t0 = Td0[s0 >> 24] ^ Td1[(s3 >> 16) & 0xff] ^ Td2[(s2 >> 8) & 0xff] ^ Td3[s1 & 0xff] ^ rk[12];
	t1 = Td0[s1 >> 24] ^ Td1[(s0 >> 16) & 0xff] ^ Td2[(s3 >> 8) & 0xff] ^ Td3[s2 & 0xff] ^ rk[13];
	t2 = Td0[s2 >> 24] ^ Td1[(s1 >> 16) & 0xff] ^ Td2[(s0 >> 8) & 0xff] ^ Td3[s3 & 0xff] ^ rk[14];
	t3 = Td0[s3 >> 24] ^ Td1[(s2 >> 16) & 0xff] ^ Td2[(s1 >> 8) & 0xff] ^ Td3[s0 & 0xff] ^ rk[15];
	/* round 4: */
	s0 = Td0[t0 >> 24] ^ Td1[(t3 >> 16) & 0xff] ^ Td2[(t2 >> 8) & 0xff] ^ Td3[t1 & 0xff] ^ rk[16];
	s1 = Td0[t1 >> 24] ^ Td1[(t0 >> 16) & 0xff] ^ Td2[(t3 >> 8) & 0xff] ^ Td3[t2 & 0xff] ^ rk[17];
	s2 = Td0[t2 >> 24] ^ Td1[(t1 >> 16) & 0xff] ^ Td2[(t0 >> 8) & 0xff] ^ Td3[t3 & 0xff] ^ rk[18];
	s3 = Td0[t3 >> 24] ^ Td1[(t2 >> 16) & 0xff] ^ Td2[(t1 >> 8) & 0xff] ^ Td3[t0 & 0xff] ^ rk[19];
	/* round 5: */
	t0 = Td0[s0 >> 24] ^ Td1[(s3 >> 16) & 0xff] ^ Td2[(s2 >> 8) & 0xff] ^ Td3[s1 & 0xff] ^ rk[20];
	t1 = Td0[s1 >> 24] ^ Td1[(s0 >> 16) & 0xff] ^ Td2[(s3 >> 8) & 0xff] ^ Td3[s2 & 0xff] ^ rk[21];
	t2 = Td0[s2 >> 24] ^ Td1[(s1 >> 16) & 0xff] ^ Td2[(s0 >> 8) & 0xff] ^ Td3[s3 & 0xff] ^ rk[22];
	t3 = Td0[s3 >> 24] ^ Td1[(s2 >> 16) & 0xff] ^ Td2[(s1 >> 8) & 0xff] ^ Td3[s0 & 0xff] ^ rk[23];
	/* round 6: */
	s0 = Td0[t0 >> 24] ^ Td1[(t3 >> 16) & 0xff] ^ Td2[(t2 >> 8) & 0xff] ^ Td3[t1 & 0xff] ^ rk[24];
	s1 = Td0[t1 >> 24] ^ Td1[(t0 >> 16) & 0xff] ^ Td2[(t3 >> 8) & 0xff] ^ Td3[t2 & 0xff] ^ rk[25];
	s2 = Td0[t2 >> 24] ^ Td1[(t1 >> 16) & 0xff] ^ Td2[(t0 >> 8) & 0xff] ^ Td3[t3 & 0xff] ^ rk[26];
	s3 = Td0[t3 >> 24] ^ Td1[(t2 >> 16) & 0xff] ^ Td2[(t1 >> 8) & 0xff] ^ Td3[t0 & 0xff] ^ rk[27];
	/* round 7: */
	t0 = Td0[s0 >> 24] ^ Td1[(s3 >> 16) & 0xff] ^ Td2[(s2 >> 8) & 0xff] ^ Td3[s1 & 0xff] ^ rk[28];
	t1 = Td0[s1 >> 24] ^ Td1[(s0 >> 16) & 0xff] ^ Td2[(s3 >> 8) & 0xff] ^ Td3[s2 & 0xff] ^ rk[29];
	t2 = Td0[s2 >> 24] ^ Td1[(s1 >> 16) & 0xff] ^ Td2[(s0 >> 8) & 0xff] ^ Td3[s3 & 0xff] ^ rk[30];
	t3 = Td0[s3 >> 24] ^ Td1[(s2 >> 16) & 0xff] ^ Td2[(s1 >> 8) & 0xff] ^ Td3[s0 & 0xff] ^ rk[31];
	/* round 8: */
	s0 = Td0[t0 >> 24] ^ Td1[(t3 >> 16) & 0xff] ^ Td2[(t2 >> 8) & 0xff] ^ Td3[t1 & 0xff] ^ rk[32];
	s1 = Td0[t1 >> 24] ^ Td1[(t0 >> 16) & 0xff] ^ Td2[(t3 >> 8) & 0xff] ^ Td3[t2 & 0xff] ^ rk[33];
	s2 = Td0[t2 >> 24] ^ Td1[(t1 >> 16) & 0xff] ^ Td2[(t0 >> 8) & 0xff] ^ Td3[t3 & 0xff] ^ rk[34];
	s3 = Td0[t3 >> 24] ^ Td1[(t2 >> 16) & 0xff] ^ Td2[(t1 >> 8) & 0xff] ^ Td3[t0 & 0xff] ^ rk[35];
	/* round 9: */
	t0 = Td0[s0 >> 24] ^ Td1[(s3 >> 16) & 0xff] ^ Td2[(s2 >> 8) & 0xff] ^ Td3[s1 & 0xff] ^ rk[36];
	t1 = Td0[s1 >> 24] ^ Td1[(s0 >> 16) & 0xff] ^ Td2[(s3 >> 8) & 0xff] ^ Td3[s2 & 0xff] ^ rk[37];
	t2 = Td0[s2 >> 24] ^ Td1[(s1 >> 16) & 0xff] ^ Td2[(s0 >> 8) & 0xff] ^ Td3[s3 & 0xff] ^ rk[38];
	t3 = Td0[s3 >> 24] ^ Td1[(s2 >> 16) & 0xff] ^ Td2[(s1 >> 8) & 0xff] ^ Td3[s0 & 0xff] ^ rk[39];
	if (key->rounds > 10) {
		/* round 10: */
		s0 = Td0[t0 >> 24] ^ Td1[(t3 >> 16) & 0xff] ^ Td2[(t2 >> 8) & 0xff] ^ Td3[t1 & 0xff] ^ rk[40];
		s1 = Td0[t1 >> 24] ^ Td1[(t0 >> 16) & 0xff] ^ Td2[(t3 >> 8) & 0xff] ^ Td3[t2 & 0xff] ^ rk[41];
		s2 = Td0[t2 >> 24] ^ Td1[(t1 >> 16) & 0xff] ^ Td2[(t0 >> 8) & 0xff] ^ Td3[t3 & 0xff] ^ rk[42];
		s3 = Td0[t3 >> 24] ^ Td1[(t2 >> 16) & 0xff] ^ Td2[(t1 >> 8) & 0xff] ^ Td3[t0 & 0xff] ^ rk[43];
		/* round 11: */
		t0 = Td0[s0 >> 24] ^ Td1[(s3 >> 16) & 0xff] ^ Td2[(s2 >> 8) & 0xff] ^ Td3[s1 & 0xff] ^ rk[44];
		t1 = Td0[s1 >> 24] ^ Td1[(s0 >> 16) & 0xff] ^ Td2[(s3 >> 8) & 0xff] ^ Td3[s2 & 0xff] ^ rk[45];
		t2 = Td0[s2 >> 24] ^ Td1[(s1 >> 16) & 0xff] ^ Td2[(s0 >> 8) & 0xff] ^ Td3[s3 & 0xff] ^ rk[46];
		t3 = Td0[s3 >> 24] ^ Td1[(s2 >> 16) & 0xff] ^ Td2[(s1 >> 8) & 0xff] ^ Td3[s0 & 0xff] ^ rk[47];
		if (key->rounds > 12) {
			/* round 12: */
			s0 = Td0[t0 >> 24] ^ Td1[(t3 >> 16) & 0xff] ^ Td2[(t2 >> 8) & 0xff] ^ Td3[t1 & 0xff] ^ rk[48];
			s1 = Td0[t1 >> 24] ^ Td1[(t0 >> 16) & 0xff] ^ Td2[(t3 >> 8) & 0xff] ^ Td3[t2 & 0xff] ^ rk[49];
			s2 = Td0[t2 >> 24] ^ Td1[(t1 >> 16) & 0xff] ^ Td2[(t0 >> 8) & 0xff] ^ Td3[t3 & 0xff] ^ rk[50];
			s3 = Td0[t3 >> 24] ^ Td1[(t2 >> 16) & 0xff] ^ Td2[(t1 >> 8) & 0xff] ^ Td3[t0 & 0xff] ^ rk[51];
			/* round 13: */
			t0 = Td0[s0 >> 24] ^ Td1[(s3 >> 16) & 0xff] ^ Td2[(s2 >> 8) & 0xff] ^ Td3[s1 & 0xff] ^ rk[52];
			t1 = Td0[s1 >> 24] ^ Td1[(s0 >> 16) & 0xff] ^ Td2[(s3 >> 8) & 0xff] ^ Td3[s2 & 0xff] ^ rk[53];
			t2 = Td0[s2 >> 24] ^ Td1[(s1 >> 16) & 0xff] ^ Td2[(s0 >> 8) & 0xff] ^ Td3[s3 & 0xff] ^ rk[54];
			t3 = Td0[s3 >> 24] ^ Td1[(s2 >> 16) & 0xff] ^ Td2[(s1 >> 8) & 0xff] ^ Td3[s0 & 0xff] ^ rk[55];
		}
	}
	rk += key->rounds << 2;
#else  /* !FULL_UNROLL */
	/*
	* Nr - 1 full rounds:
	*/
	r = key->rounds >> 1;
	for (;;) {
		t0 =
			Td0[(s0 >> 24)] ^
			Td1[(s3 >> 16) & 0xff] ^
			Td2[(s2 >> 8) & 0xff] ^
			Td3[(s1)& 0xff] ^
			rk[4];
		t1 =
			Td0[(s1 >> 24)] ^
			Td1[(s0 >> 16) & 0xff] ^
			Td2[(s3 >> 8) & 0xff] ^
			Td3[(s2)& 0xff] ^
			rk[5];
		t2 =
			Td0[(s2 >> 24)] ^
			Td1[(s1 >> 16) & 0xff] ^
			Td2[(s0 >> 8) & 0xff] ^
			Td3[(s3)& 0xff] ^
			rk[6];
		t3 =
			Td0[(s3 >> 24)] ^
			Td1[(s2 >> 16) & 0xff] ^
			Td2[(s1 >> 8) & 0xff] ^
			Td3[(s0)& 0xff] ^
			rk[7];

		rk += 8;
		if (--r == 0) {
			break;
		}

		s0 =
			Td0[(t0 >> 24)] ^
			Td1[(t3 >> 16) & 0xff] ^
			Td2[(t2 >> 8) & 0xff] ^
			Td3[(t1)& 0xff] ^
			rk[0];
		s1 =
			Td0[(t1 >> 24)] ^
			Td1[(t0 >> 16) & 0xff] ^
			Td2[(t3 >> 8) & 0xff] ^
			Td3[(t2)& 0xff] ^
			rk[1];
		s2 =
			Td0[(t2 >> 24)] ^
			Td1[(t1 >> 16) & 0xff] ^
			Td2[(t0 >> 8) & 0xff] ^
			Td3[(t3)& 0xff] ^
			rk[2];
		s3 =
			Td0[(t3 >> 24)] ^
			Td1[(t2 >> 16) & 0xff] ^
			Td2[(t1 >> 8) & 0xff] ^
			Td3[(t0)& 0xff] ^
			rk[3];
	}
#endif /* ?FULL_UNROLL */
	/*
	* apply last round and
	* map cipher state to byte array block:
	*/
	s0 =
		((u32)Td4[(t0 >> 24)] << 24) ^
		((u32)Td4[(t3 >> 16) & 0xff] << 16) ^
		((u32)Td4[(t2 >> 8) & 0xff] << 8) ^
		((u32)Td4[(t1)& 0xff]) ^
		rk[0];
	PUTU32(out, s0);
	s1 =
		((u32)Td4[(t1 >> 24)] << 24) ^
		((u32)Td4[(t0 >> 16) & 0xff] << 16) ^
		((u32)Td4[(t3 >> 8) & 0xff] << 8) ^
		((u32)Td4[(t2)& 0xff]) ^
		rk[1];
	PUTU32(out + 4, s1);
	s2 =
		((u32)Td4[(t2 >> 24)] << 24) ^
		((u32)Td4[(t1 >> 16) & 0xff] << 16) ^
		((u32)Td4[(t0 >> 8) & 0xff] << 8) ^
		((u32)Td4[(t3)& 0xff]) ^
		rk[2];
	PUTU32(out + 8, s2);
	s3 =
		((u32)Td4[(t3 >> 24)] << 24) ^
		((u32)Td4[(t2 >> 16) & 0xff] << 16) ^
		((u32)Td4[(t1 >> 8) & 0xff] << 8) ^
		((u32)Td4[(t0)& 0xff]) ^
		rk[3];
	PUTU32(out + 12, s3);
}

void AES_cbc_decrypt(const unsigned char *in, unsigned char *out,
	size_t len, const AES_KEY *key,
	unsigned char *ivec)
{
			CRYPTO_cbc128_decrypt(in, out, len, key, ivec,
		(block128_f)AES_decrypt);
}


//////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////

extern char* gPkgNameC;
extern char* gFilesDirC;

MonoImage *
mono_image_open_from_data_with_name (char *data, guint32 data_len, gboolean need_copy, MonoImageOpenStatus *status, gboolean refonly, const char *name)
{
	LOGD("$$ _image_open_from_data_with_name name:%s", name);
	gboolean isHotReload = 0;
	//if(strstr(name,"Assembly-CSharp.dll")){
	int filesCnt = gHotFilesC->len;
	int i=0;
	while(i<filesCnt){
	LOGD("$$ match dll.");
	  char* hotFileName = g_array_index(gHotFilesC, char*, i);
	  i++;
	  int fileNmLen = strlen(hotFileName);
	  int nmLen = strlen(name);
	  LOGD("fileNmLen:%i nmLen:%i", fileNmLen, nmLen);

	  if(fileNmLen>nmLen) continue;
	  //char matchNm[fileNmLen];
	  //memcpy(&matchNm,  
	 char* lastNm = name + (nmLen-fileNmLen); 
	 if(0!=strcmp(lastNm, hotFileName)) continue;
	  
	  isHotReload = 1;
	  FILE * pFile;
	  LOGD("strcat name");
	  char dllPath[512];
	  memset(&dllPath,'\0',512);
	  strcat(&dllPath,gFilesDirC);
	  strcat(&dllPath,"/Managed/");
          strcat(&dllPath, hotFileName); 
	  //"/Managed/Assembly-CSharp.dll");
          LOGD("start load dll path:%s", &dllPath);
	  pFile = fopen(&dllPath, "rb");
	  if(pFile!=NULL){
	    LOGD("file opened");
      	    fseek (pFile , 0 , SEEK_END);
	    long lSize = ftell(pFile);
	    rewind(pFile);
	    char* buffer = (char*) g_try_malloc(sizeof(char)*lSize);
	    int res = fread(buffer,1,lSize,pFile);
	    if(res==lSize){
	      LOGD("_ASM_CS load success size:%i",lSize);
	      data = buffer;
	      data_len = lSize;
	    }
	   LOGD("close file");
	   fclose(pFile);
	   LOGD("close file finished");
	  }
	}

	MonoCLIImageInfo *iinfo;
	MonoImage *image;
	char *datac;

	if (!data || !data_len) {
		if (status)
			*status = MONO_IMAGE_IMAGE_INVALID;
		return NULL;
	}
	gboolean isCrypt = 0;
	if(data[data_len-1]==58 && data[data_len-2]==58 && data[data_len-3]==58 && data[data_len-4]==58)
	{
		isCrypt = 1;
		data_len -= 5;
		const unsigned char* keydata = (const unsigned char*) "PASSWARD";
		unsigned char* iv = (unsigned char*) g_try_malloc(sizeof(unsigned char) * 16);
		memset(iv, 88, 16);

		AES_KEY key;
		private_AES_set_decrypt_key(keydata, 128, &key);

		unsigned char* deData = (unsigned char*) g_try_malloc(sizeof(unsigned char) * data_len); 
		AES_cbc_decrypt((unsigned char*)data, deData, data_len, &key, iv);
		
		data_len = data_len  - (unsigned int)data[data_len];
		//g_free(data);
		data = (char*) g_try_malloc(data_len);

		memcpy(data, deData, data_len);
		g_free(deData);
		g_free(iv);
	}
	
	datac = data;

	//crypt data has copy 
	if (!isCrypt && need_copy) {
		datac = g_try_malloc (data_len);
		if (!datac) {
			if (status)
				*status = MONO_IMAGE_ERROR_ERRNO;
			return NULL;
		}
		memcpy (datac, data, data_len);
	}

	image = g_new0 (MonoImage, 1);
	image->raw_data = datac;
	image->raw_data_len = data_len;
	image->raw_data_allocated = need_copy;
	image->name = (name == NULL) ? g_strdup_printf ("data-%p", datac) : g_strdup(name);
	iinfo = g_new0 (MonoCLIImageInfo, 1);
	image->image_info = iinfo;
	image->ref_only = refonly;
	image->ref_count = 1;

	image = do_mono_image_load (image, status, TRUE, TRUE);
	if (image == NULL)
		return NULL;

	return register_image (image);
}

MonoImage *
mono_image_open_from_data_full (char *data, guint32 data_len, gboolean need_copy, MonoImageOpenStatus *status, gboolean refonly)
{
  return mono_image_open_from_data_with_name (data, data_len, need_copy, status, refonly, NULL);
}

MonoImage *
mono_image_open_from_data (char *data, guint32 data_len, gboolean need_copy, MonoImageOpenStatus *status)
{
	return mono_image_open_from_data_full (data, data_len, need_copy, status, FALSE);
}

#ifdef USE_COREE
/* fname is not duplicated. */
MonoImage*
mono_image_open_from_module_handle (HMODULE module_handle, char* fname, gboolean has_entry_point, MonoImageOpenStatus* status)
{
	MonoImage* image;
	MonoCLIImageInfo* iinfo;

	image = g_new0 (MonoImage, 1);
	image->raw_data = (char*) module_handle;
	image->is_module_handle = TRUE;
	iinfo = g_new0 (MonoCLIImageInfo, 1);
	image->image_info = iinfo;
	image->name = fname;
	image->ref_count = has_entry_point ? 0 : 1;
	image->has_entry_point = has_entry_point;

	image = do_mono_image_load (image, status, TRUE, TRUE);
	if (image == NULL)
		return NULL;

	return register_image (image);
}
#endif

MonoImage *
mono_image_open_full (const char *fname, MonoImageOpenStatus *status, gboolean refonly)
{
	MonoImage *image;
	GHashTable *loaded_images;
	char *absfname;
	
	g_return_val_if_fail (fname != NULL, NULL);
	
#ifdef USE_COREE
	/* Load modules using LoadLibrary. */
	if (!refonly && coree_module_handle) {
		HMODULE module_handle;
		guint16 *fname_utf16;
		DWORD last_error;

		absfname = mono_path_resolve_symlinks (fname);
		fname_utf16 = NULL;

		/* There is little overhead because the OS loader lock is held by LoadLibrary. */
		mono_images_lock ();
		image = g_hash_table_lookup (loaded_images_hash, absfname);
		if (image) {
			g_assert (image->is_module_handle);
			if (image->has_entry_point && image->ref_count == 0) {
				/* Increment reference count on images loaded outside of the runtime. */
				fname_utf16 = g_utf8_to_utf16 (absfname, -1, NULL, NULL, NULL);
				/* The image is already loaded because _CorDllMain removes images from the hash. */
				module_handle = LoadLibrary (fname_utf16);
				g_assert (module_handle == (HMODULE) image->raw_data);
			}
			mono_image_addref (image);
			mono_images_unlock ();
			if (fname_utf16)
				g_free (fname_utf16);
			g_free (absfname);
			return image;
		}

		fname_utf16 = g_utf8_to_utf16 (absfname, -1, NULL, NULL, NULL);
		module_handle = MonoLoadImage (fname_utf16);
		if (status && module_handle == NULL)
			last_error = GetLastError ();

		/* mono_image_open_from_module_handle is called by _CorDllMain. */
		image = g_hash_table_lookup (loaded_images_hash, absfname);
		if (image)
			mono_image_addref (image);
		mono_images_unlock ();

		g_free (fname_utf16);

		if (module_handle == NULL) {
			g_assert (!image);
			g_free (absfname);
			if (status) {
				if (last_error == ERROR_BAD_EXE_FORMAT || last_error == STATUS_INVALID_IMAGE_FORMAT)
					*status = MONO_IMAGE_IMAGE_INVALID;
				else
					*status = MONO_IMAGE_ERROR_ERRNO;
			}
			return NULL;
		}

		if (image) {
			g_assert (image->is_module_handle);
			g_assert (image->has_entry_point);
			g_free (absfname);
			return image;
		}

		return mono_image_open_from_module_handle (module_handle, absfname, FALSE, status);
	}
#endif

	absfname = mono_path_canonicalize (fname);

	/*
	 * The easiest solution would be to do all the loading inside the mutex,
	 * but that would lead to scalability problems. So we let the loading
	 * happen outside the mutex, and if multiple threads happen to load
	 * the same image, we discard all but the first copy.
	 */
	mono_images_lock ();
	loaded_images = refonly ? loaded_images_refonly_hash : loaded_images_hash;
	image = g_hash_table_lookup (loaded_images, absfname);
	g_free (absfname);
	
	if (image){
		mono_image_addref (image);
		mono_images_unlock ();
		return image;
	}
	mono_images_unlock ();

	image = do_mono_image_open (fname, status, TRUE, TRUE, refonly);
	if (image == NULL)
		return NULL;

	return register_image (image);
}

/**
 * mono_image_open:
 * @fname: filename that points to the module we want to open
 * @status: An error condition is returned in this field
 *
 * Returns: An open image of type %MonoImage or NULL on error. 
 * The caller holds a temporary reference to the returned image which should be cleared 
 * when no longer needed by calling mono_image_close ().
 * if NULL, then check the value of @status for details on the error
 */
MonoImage *
mono_image_open (const char *fname, MonoImageOpenStatus *status)
{
	return mono_image_open_full (fname, status, FALSE);
}

/**
 * mono_pe_file_open:
 * @fname: filename that points to the module we want to open
 * @status: An error condition is returned in this field
 *
 * Returns: An open image of type %MonoImage or NULL on error.  if
 * NULL, then check the value of @status for details on the error.
 * This variant for mono_image_open DOES NOT SET UP CLI METADATA.
 * It's just a PE file loader, used for FileVersionInfo.  It also does
 * not use the image cache.
 */
MonoImage *
mono_pe_file_open (const char *fname, MonoImageOpenStatus *status)
{
	g_return_val_if_fail (fname != NULL, NULL);
	
	return(do_mono_image_open (fname, status, FALSE, TRUE, FALSE));
}

/**
 * mono_image_open_raw
 * @fname: filename that points to the module we want to open
 * @status: An error condition is returned in this field
 * 
 * Returns an image without loading neither pe or cli data.
 * 
 * Use mono_image_load_pe_data and mono_image_load_cli_data to load them.  
 */
MonoImage *
mono_image_open_raw (const char *fname, MonoImageOpenStatus *status)
{
	g_return_val_if_fail (fname != NULL, NULL);
	
	return(do_mono_image_open (fname, status, FALSE, FALSE, FALSE));
}

void
mono_image_fixup_vtable (MonoImage *image)
{
#ifdef USE_COREE
	MonoCLIImageInfo *iinfo;
	MonoPEDirEntry *de;
	MonoVTableFixup *vtfixup;
	int count;
	gpointer slot;
	guint16 slot_type;
	int slot_count;

	g_assert (image->is_module_handle);

	iinfo = image->image_info;
	de = &iinfo->cli_cli_header.ch_vtable_fixups;
	if (!de->rva || !de->size)
		return;
	vtfixup = (MonoVTableFixup*) mono_image_rva_map (image, de->rva);
	if (!vtfixup)
		return;
	
	count = de->size / sizeof (MonoVTableFixup);
	while (count--) {
		if (!vtfixup->rva || !vtfixup->count)
			continue;

		slot = mono_image_rva_map (image, vtfixup->rva);
		g_assert (slot);
		slot_type = vtfixup->type;
		slot_count = vtfixup->count;
		if (slot_type & VTFIXUP_TYPE_32BIT)
			while (slot_count--) {
				*((guint32*) slot) = (guint32) mono_marshal_get_vtfixup_ftnptr (image, *((guint32*) slot), slot_type);
				slot = ((guint32*) slot) + 1;
			}
		else if (slot_type & VTFIXUP_TYPE_64BIT)
			while (slot_count--) {
				*((guint64*) slot) = (guint64) mono_marshal_get_vtfixup_ftnptr (image, *((guint64*) slot), slot_type);
				slot = ((guint32*) slot) + 1;
			}
		else
			g_assert_not_reached();

		vtfixup++;
	}
#else
	g_assert_not_reached();
#endif
}

static void
free_hash_table (gpointer key, gpointer val, gpointer user_data)
{
	g_hash_table_destroy ((GHashTable*)val);
}

/*
static void
free_mr_signatures (gpointer key, gpointer val, gpointer user_data)
{
	mono_metadata_free_method_signature ((MonoMethodSignature*)val);
}
*/

static void
free_remoting_wrappers (gpointer key, gpointer val, gpointer user_data)
{
	g_free (val);
}

static void
free_array_cache_entry (gpointer key, gpointer val, gpointer user_data)
{
	g_slist_free ((GSList*)val);
}

/**
 * mono_image_addref:
 * @image: The image file we wish to add a reference to
 *
 *  Increases the reference count of an image.
 */
void
mono_image_addref (MonoImage *image)
{
	InterlockedIncrement (&image->ref_count);
}	

void
mono_dynamic_stream_reset (MonoDynamicStream* stream)
{
	stream->alloc_size = stream->index = stream->offset = 0;
	g_free (stream->data);
	stream->data = NULL;
	if (stream->hash) {
		g_hash_table_destroy (stream->hash);
		stream->hash = NULL;
	}
}

static inline void
free_hash (GHashTable *hash)
{
	if (hash)
		g_hash_table_destroy (hash);
}

/**
 * mono_image_close:
 * @image: The image file we wish to close
 *
 * Closes an image file, deallocates all memory consumed and
 * unmaps all possible sections of the file
 */
void
mono_image_close (MonoImage *image)
{
	MonoImage *image2;
	GHashTable *loaded_images;
	int i;

	g_return_if_fail (image != NULL);

	/* 
	 * Atomically decrement the refcount and remove ourselves from the hash tables, so
	 * register_image () can't grab an image which is being closed.
	 */
	mono_images_lock ();

	if (InterlockedDecrement (&image->ref_count) > 0) {
		mono_images_unlock ();
		return;
	}

	loaded_images = image->ref_only ? loaded_images_refonly_hash : loaded_images_hash;
	image2 = g_hash_table_lookup (loaded_images, image->name);
	if (image == image2) {
		/* This is not true if we are called from mono_image_open () */
		g_hash_table_remove (loaded_images, image->name);
	}
	if (image->assembly_name && (g_hash_table_lookup (loaded_images, image->assembly_name) == image))
		g_hash_table_remove (loaded_images, (char *) image->assembly_name);	

	mono_images_unlock ();

#ifdef USE_COREE
	if (image->is_module_handle && image->has_entry_point) {
		mono_images_lock ();
		if (image->ref_count == 0) {
			/* Image will be closed by _CorDllMain. */
			FreeLibrary ((HMODULE) image->raw_data);
			mono_images_unlock ();
			return;
		}
		mono_images_unlock ();
	}
#endif

	mono_profiler_module_event (image, MONO_PROFILE_START_UNLOAD);

	mono_trace (G_LOG_LEVEL_INFO, MONO_TRACE_ASSEMBLY, "Unloading image %s [%p].", image->name, image);

	mono_metadata_clean_for_image (image);

	/*
	 * The caches inside a MonoImage might refer to metadata which is stored in referenced 
	 * assemblies, so we can't release these references in mono_assembly_close () since the
	 * MonoImage might outlive its associated MonoAssembly.
	 */
	if (image->references && !image->dynamic) {
		MonoTableInfo *t = &image->tables [MONO_TABLE_ASSEMBLYREF];
		int i;

		for (i = 0; i < t->rows; i++) {
			if (image->references [i])
				mono_assembly_close (image->references [i]);
		}

		g_free (image->references);
		image->references = NULL;
	}

#ifdef USE_COREE
	mono_images_lock ();
	if (image->is_module_handle && !image->has_entry_point)
		FreeLibrary ((HMODULE) image->raw_data);
	mono_images_unlock ();
#endif

	if (image->raw_buffer_used) {
		if (image->raw_data != NULL)
			mono_file_unmap (image->raw_data, image->raw_data_handle);
	}
	
	if (image->raw_data_allocated) {
		/* FIXME: do we need this? (image is disposed anyway) */
		/* image->raw_metadata and cli_sections might lie inside image->raw_data */
		MonoCLIImageInfo *ii = image->image_info;

		if ((image->raw_metadata > image->raw_data) &&
			(image->raw_metadata <= (image->raw_data + image->raw_data_len)))
			image->raw_metadata = NULL;

		for (i = 0; i < ii->cli_section_count; i++)
			if (((char*)(ii->cli_sections [i]) > image->raw_data) &&
				((char*)(ii->cli_sections [i]) <= ((char*)image->raw_data + image->raw_data_len)))
				ii->cli_sections [i] = NULL;

		g_free (image->raw_data);
	}

	if (debug_assembly_unload) {
		image->name = g_strdup_printf ("%s - UNLOADED", image->name);
	} else {
		g_free (image->name);
		g_free (image->guid);
		g_free (image->version);
		g_free (image->files);
	}

	if (image->method_cache)
		g_hash_table_destroy (image->method_cache);
	if (image->methodref_cache)
		g_hash_table_destroy (image->methodref_cache);
	mono_internal_hash_table_destroy (&image->class_cache);
	g_hash_table_destroy (image->field_cache);
	if (image->array_cache) {
		g_hash_table_foreach (image->array_cache, free_array_cache_entry, NULL);
		g_hash_table_destroy (image->array_cache);
	}
	if (image->szarray_cache)
		g_hash_table_destroy (image->szarray_cache);
	if (image->ptr_cache)
		g_hash_table_destroy (image->ptr_cache);
	if (image->name_cache) {
		g_hash_table_foreach (image->name_cache, free_hash_table, NULL);
		g_hash_table_destroy (image->name_cache);
	}

	free_hash (image->native_wrapper_cache);
	free_hash (image->managed_wrapper_cache);
	free_hash (image->delegate_begin_invoke_cache);
	free_hash (image->delegate_end_invoke_cache);
	free_hash (image->delegate_invoke_cache);
	free_hash (image->delegate_abstract_invoke_cache);
	if (image->remoting_invoke_cache)
		g_hash_table_foreach (image->remoting_invoke_cache, free_remoting_wrappers, NULL);
	free_hash (image->remoting_invoke_cache);
	free_hash (image->runtime_invoke_cache);
	free_hash (image->runtime_invoke_direct_cache);
	free_hash (image->runtime_invoke_vcall_cache);
	free_hash (image->synchronized_cache);
	free_hash (image->unbox_wrapper_cache);
	free_hash (image->cominterop_invoke_cache);
	free_hash (image->cominterop_wrapper_cache);
	free_hash (image->typespec_cache);
	free_hash (image->ldfld_wrapper_cache);
	free_hash (image->ldflda_wrapper_cache);
	free_hash (image->stfld_wrapper_cache);
	free_hash (image->isinst_cache);
	free_hash (image->castclass_cache);
	free_hash (image->proxy_isinst_cache);
	free_hash (image->thunk_invoke_cache);

	/* The ownership of signatures is not well defined */
	//g_hash_table_foreach (image->memberref_signatures, free_mr_signatures, NULL);
	g_hash_table_destroy (image->memberref_signatures);
	//g_hash_table_foreach (image->helper_signatures, free_mr_signatures, NULL);
	g_hash_table_destroy (image->helper_signatures);
	g_hash_table_destroy (image->method_signatures);

	if (image->generic_class_cache)
		g_hash_table_destroy (image->generic_class_cache);

	if (image->rgctx_template_hash)
		g_hash_table_destroy (image->rgctx_template_hash);

	if (image->property_hash)
		mono_property_hash_destroy (image->property_hash);

	g_slist_free (image->reflection_info_unregister_classes);

	if (image->interface_bitset) {
		mono_unload_interface_ids (image->interface_bitset);
		mono_bitset_free (image->interface_bitset);
	}
	if (image->image_info){
		MonoCLIImageInfo *ii = image->image_info;

		if (ii->cli_section_tables)
			g_free (ii->cli_section_tables);
		if (ii->cli_sections)
			g_free (ii->cli_sections);
		g_free (image->image_info);
	}

	for (i = 0; i < image->module_count; ++i) {
		if (image->modules [i])
			mono_image_close (image->modules [i]);
	}
	if (image->modules)
		g_free (image->modules);
	if (image->modules_loaded)
		g_free (image->modules_loaded);
	if (image->references)
		g_free (image->references);
	mono_perfcounters->loader_bytes -= mono_mempool_get_allocated (image->mempool);

	DeleteCriticalSection (&image->szarray_cache_lock);
	DeleteCriticalSection (&image->lock);

	/*g_print ("destroy image %p (dynamic: %d)\n", image, image->dynamic);*/
	if (!image->dynamic) {
		if (debug_assembly_unload)
			mono_mempool_invalidate (image->mempool);
		else {
			mono_mempool_destroy (image->mempool);
			g_free (image);
		}
	} else {
		/* Dynamic images are GC_MALLOCed */
		g_free ((char*)image->module_name);
		mono_dynamic_image_free ((MonoDynamicImage*)image);
		if (debug_assembly_unload)
			mono_mempool_invalidate (image->mempool);
		else
			mono_mempool_destroy (image->mempool);
	}

	mono_profiler_module_event (image, MONO_PROFILE_END_UNLOAD);
}

/** 
 * mono_image_strerror:
 * @status: an code indicating the result from a recent operation
 *
 * Returns: a string describing the error
 */
const char *
mono_image_strerror (MonoImageOpenStatus status)
{
	switch (status){
	case MONO_IMAGE_OK:
		return "success";
	case MONO_IMAGE_ERROR_ERRNO:
		return strerror (errno);
	case MONO_IMAGE_IMAGE_INVALID:
		return "File does not contain a valid CIL image";
	case MONO_IMAGE_MISSING_ASSEMBLYREF:
		return "An assembly was referenced, but could not be found";
	}
	return "Internal error";
}

static gpointer
mono_image_walk_resource_tree (MonoCLIImageInfo *info, guint32 res_id,
			       guint32 lang_id, gunichar2 *name,
			       MonoPEResourceDirEntry *entry,
			       MonoPEResourceDir *root, guint32 level)
{
	gboolean is_string, is_dir;
	guint32 name_offset, dir_offset;

	/* Level 0 holds a directory entry for each type of resource
	 * (identified by ID or name).
	 *
	 * Level 1 holds a directory entry for each named resource
	 * item, and each "anonymous" item of a particular type of
	 * resource.
	 *
	 * Level 2 holds a directory entry for each language pointing to
	 * the actual data.
	 */
	is_string = MONO_PE_RES_DIR_ENTRY_NAME_IS_STRING (*entry);
	name_offset = MONO_PE_RES_DIR_ENTRY_NAME_OFFSET (*entry);

	is_dir = MONO_PE_RES_DIR_ENTRY_IS_DIR (*entry);
	dir_offset = MONO_PE_RES_DIR_ENTRY_DIR_OFFSET (*entry);

	if(level==0) {
		if (is_string)
			return NULL;
	} else if (level==1) {
		if (res_id != name_offset)
			return NULL;
#if 0
		if(name!=NULL &&
		   is_string==TRUE && name!=lookup (name_offset)) {
			return(NULL);
		}
#endif
	} else if (level==2) {
		if (is_string == TRUE || (is_string == FALSE && lang_id != 0 && name_offset != lang_id))
			return NULL;
	} else {
		g_assert_not_reached ();
	}

	if(is_dir==TRUE) {
		MonoPEResourceDir *res_dir=(MonoPEResourceDir *)(((char *)root)+dir_offset);
		MonoPEResourceDirEntry *sub_entries=(MonoPEResourceDirEntry *)(res_dir+1);
		guint32 entries, i;

		entries = GUINT16_FROM_LE (res_dir->res_named_entries) + GUINT16_FROM_LE (res_dir->res_id_entries);

		for(i=0; i<entries; i++) {
			MonoPEResourceDirEntry *sub_entry=&sub_entries[i];
			gpointer ret;
			
			ret=mono_image_walk_resource_tree (info, res_id,
							   lang_id, name,
							   sub_entry, root,
							   level+1);
			if(ret!=NULL) {
				return(ret);
			}
		}

		return(NULL);
	} else {
		MonoPEResourceDataEntry *data_entry=(MonoPEResourceDataEntry *)((char *)(root)+dir_offset);
		MonoPEResourceDataEntry *res;

		res = g_new0 (MonoPEResourceDataEntry, 1);

		res->rde_data_offset = GUINT32_TO_LE (data_entry->rde_data_offset);
		res->rde_size = GUINT32_TO_LE (data_entry->rde_size);
		res->rde_codepage = GUINT32_TO_LE (data_entry->rde_codepage);
		res->rde_reserved = GUINT32_TO_LE (data_entry->rde_reserved);

		return (res);
	}
}

/**
 * mono_image_lookup_resource:
 * @image: the image to look up the resource in
 * @res_id: A MONO_PE_RESOURCE_ID_ that represents the resource ID to lookup.
 * @lang_id: The language id.
 * @name: the resource name to lookup.
 *
 * Returns: NULL if not found, otherwise a pointer to the in-memory representation
 * of the given resource. The caller should free it using g_free () when no longer
 * needed.
 */
gpointer
mono_image_lookup_resource (MonoImage *image, guint32 res_id, guint32 lang_id, gunichar2 *name)
{
	MonoCLIImageInfo *info;
	MonoDotNetHeader *header;
	MonoPEDatadir *datadir;
	MonoPEDirEntry *rsrc;
	MonoPEResourceDir *resource_dir;
	MonoPEResourceDirEntry *res_entries;
	guint32 entries, i;

	if(image==NULL) {
		return(NULL);
	}

	mono_image_ensure_section_idx (image, MONO_SECTION_RSRC);

	info=image->image_info;
	if(info==NULL) {
		return(NULL);
	}

	header=&info->cli_header;
	if(header==NULL) {
		return(NULL);
	}

	datadir=&header->datadir;
	if(datadir==NULL) {
		return(NULL);
	}

	rsrc=&datadir->pe_resource_table;
	if(rsrc==NULL) {
		return(NULL);
	}

	resource_dir=(MonoPEResourceDir *)mono_image_rva_map (image, rsrc->rva);
	if(resource_dir==NULL) {
		return(NULL);
	}

	entries = GUINT16_FROM_LE (resource_dir->res_named_entries) + GUINT16_FROM_LE (resource_dir->res_id_entries);
	res_entries=(MonoPEResourceDirEntry *)(resource_dir+1);
	
	for(i=0; i<entries; i++) {
		MonoPEResourceDirEntry *entry=&res_entries[i];
		gpointer ret;
		
		ret=mono_image_walk_resource_tree (info, res_id, lang_id,
						   name, entry, resource_dir,
						   0);
		if(ret!=NULL) {
			return(ret);
		}
	}

	return(NULL);
}

/** 
 * mono_image_get_entry_point:
 * @image: the image where the entry point will be looked up.
 *
 * Use this routine to determine the metadata token for method that
 * has been flagged as the entry point.
 *
 * Returns: the token for the entry point method in the image
 */
guint32
mono_image_get_entry_point (MonoImage *image)
{
	return ((MonoCLIImageInfo*)image->image_info)->cli_cli_header.ch_entry_point;
}

/**
 * mono_image_get_resource:
 * @image: the image where the resource will be looked up.
 * @offset: The offset to add to the resource
 * @size: a pointer to an int where the size of the resource will be stored
 *
 * This is a low-level routine that fetches a resource from the
 * metadata that starts at a given @offset.  The @size parameter is
 * filled with the data field as encoded in the metadata.
 *
 * Returns: the pointer to the resource whose offset is @offset.
 */
const char*
mono_image_get_resource (MonoImage *image, guint32 offset, guint32 *size)
{
	MonoCLIImageInfo *iinfo = image->image_info;
	MonoCLIHeader *ch = &iinfo->cli_cli_header;
	const char* data;

	if (!ch->ch_resources.rva || offset + 4 > ch->ch_resources.size)
		return NULL;
	
	data = mono_image_rva_map (image, ch->ch_resources.rva);
	if (!data)
		return NULL;
	data += offset;
	if (size)
		*size = read32 (data);
	data += 4;
	return data;
}

MonoImage*
mono_image_load_file_for_image (MonoImage *image, int fileidx)
{
	char *base_dir, *name;
	MonoImage *res;
	MonoTableInfo  *t = &image->tables [MONO_TABLE_FILE];
	const char *fname;
	guint32 fname_id;

	if (fileidx < 1 || fileidx > t->rows)
		return NULL;

	mono_loader_lock ();
	if (image->files && image->files [fileidx - 1]) {
		mono_loader_unlock ();
		return image->files [fileidx - 1];
	}

	if (!image->files)
		image->files = g_new0 (MonoImage*, t->rows);

	fname_id = mono_metadata_decode_row_col (t, fileidx - 1, MONO_FILE_NAME);
	fname = mono_metadata_string_heap (image, fname_id);
	base_dir = g_path_get_dirname (image->name);
	name = g_build_filename (base_dir, fname, NULL);
	res = mono_image_open (name, NULL);
	if (res) {
		int i;
		/* g_print ("loaded file %s from %s (%p)\n", name, image->name, image->assembly); */
		res->assembly = image->assembly;
		for (i = 0; i < res->module_count; ++i) {
			if (res->modules [i] && !res->modules [i]->assembly)
				res->modules [i]->assembly = image->assembly;
		}

		image->files [fileidx - 1] = res;
#ifdef USE_COREE
		if (res->is_module_handle)
			mono_image_fixup_vtable (res);
#endif
	}
	mono_loader_unlock ();
	g_free (name);
	g_free (base_dir);
	return res;
}

/**
 * mono_image_get_strong_name:
 * @image: a MonoImage
 * @size: a guint32 pointer, or NULL.
 *
 * If the image has a strong name, and @size is not NULL, the value
 * pointed to by size will have the size of the strong name.
 *
 * Returns: NULL if the image does not have a strong name, or a
 * pointer to the public key.
 */
const char*
mono_image_get_strong_name (MonoImage *image, guint32 *size)
{
	MonoCLIImageInfo *iinfo = image->image_info;
	MonoPEDirEntry *de = &iinfo->cli_cli_header.ch_strong_name;
	const char* data;

	if (!de->size || !de->rva)
		return NULL;
	data = mono_image_rva_map (image, de->rva);
	if (!data)
		return NULL;
	if (size)
		*size = de->size;
	return data;
}

/**
 * mono_image_strong_name_position:
 * @image: a MonoImage
 * @size: a guint32 pointer, or NULL.
 *
 * If the image has a strong name, and @size is not NULL, the value
 * pointed to by size will have the size of the strong name.
 *
 * Returns: the position within the image file where the strong name
 * is stored.
 */
guint32
mono_image_strong_name_position (MonoImage *image, guint32 *size)
{
	MonoCLIImageInfo *iinfo = image->image_info;
	MonoPEDirEntry *de = &iinfo->cli_cli_header.ch_strong_name;
	guint32 pos;

	if (size)
		*size = de->size;
	if (!de->size || !de->rva)
		return 0;
	pos = mono_cli_rva_image_map (image, de->rva);
	return pos == INVALID_ADDRESS ? 0 : pos;
}

/**
 * mono_image_get_public_key:
 * @image: a MonoImage
 * @size: a guint32 pointer, or NULL.
 *
 * This is used to obtain the public key in the @image.
 * 
 * If the image has a public key, and @size is not NULL, the value
 * pointed to by size will have the size of the public key.
 * 
 * Returns: NULL if the image does not have a public key, or a pointer
 * to the public key.
 */
const char*
mono_image_get_public_key (MonoImage *image, guint32 *size)
{
	const char *pubkey;
	guint32 len, tok;

	if (image->dynamic) {
		if (size)
			*size = ((MonoDynamicImage*)image)->public_key_len;
		return (char*)((MonoDynamicImage*)image)->public_key;
	}
	if (image->tables [MONO_TABLE_ASSEMBLY].rows != 1)
		return NULL;
	tok = mono_metadata_decode_row_col (&image->tables [MONO_TABLE_ASSEMBLY], 0, MONO_ASSEMBLY_PUBLIC_KEY);
	if (!tok)
		return NULL;
	pubkey = mono_metadata_blob_heap (image, tok);
	len = mono_metadata_decode_blob_size (pubkey, &pubkey);
	if (size)
		*size = len;
	return pubkey;
}

/**
 * mono_image_get_name:
 * @name: a MonoImage
 *
 * Returns: the name of the assembly.
 */
const char*
mono_image_get_name (MonoImage *image)
{
	return image->assembly_name;
}

/**
 * mono_image_get_filename:
 * @image: a MonoImage
 *
 * Used to get the filename that hold the actual MonoImage
 *
 * Returns: the filename.
 */
const char*
mono_image_get_filename (MonoImage *image)
{
	return image->name;
}

const char*
mono_image_get_guid (MonoImage *image)
{
	return image->guid;
}

const MonoTableInfo*
mono_image_get_table_info (MonoImage *image, int table_id)
{
	if (table_id < 0 || table_id >= MONO_TABLE_NUM)
		return NULL;
	return &image->tables [table_id];
}

int
mono_image_get_table_rows (MonoImage *image, int table_id)
{
	if (table_id < 0 || table_id >= MONO_TABLE_NUM)
		return 0;
	return image->tables [table_id].rows;
}

int
mono_table_info_get_rows (const MonoTableInfo *table)
{
	return table->rows;
}

/**
 * mono_image_get_assembly:
 * @image: the MonoImage.
 *
 * Use this routine to get the assembly that owns this image.
 *
 * Returns: the assembly that holds this image.
 */
MonoAssembly* 
mono_image_get_assembly (MonoImage *image)
{
	return image->assembly;
}

/**
 * mono_image_is_dynamic:
 * @image: the MonoImage
 *
 * Determines if the given image was created dynamically through the
 * System.Reflection.Emit API
 *
 * Returns: TRUE if the image was created dynamically, FALSE if not.
 */
gboolean
mono_image_is_dynamic (MonoImage *image)
{
	return image->dynamic;
}

/**
 * mono_image_has_authenticode_entry:
 * @image: the MonoImage
 *
 * Use this routine to determine if the image has a Authenticode
 * Certificate Table.
 *
 * Returns: TRUE if the image contains an authenticode entry in the PE
 * directory.
 */
gboolean
mono_image_has_authenticode_entry (MonoImage *image)
{
	MonoCLIImageInfo *iinfo = image->image_info;
	MonoDotNetHeader *header = &iinfo->cli_header;
	MonoPEDirEntry *de = &header->datadir.pe_certificate_table;
	// the Authenticode "pre" (non ASN.1) header is 8 bytes long
	return ((de->rva != 0) && (de->size > 8));
}

gpointer
mono_image_alloc (MonoImage *image, guint size)
{
	gpointer res;

	mono_perfcounters->loader_bytes += size;
	mono_image_lock (image);
	res = mono_mempool_alloc (image->mempool, size);
	mono_image_unlock (image);

	return res;
}

gpointer
mono_image_alloc0 (MonoImage *image, guint size)
{
	gpointer res;

	mono_perfcounters->loader_bytes += size;
	mono_image_lock (image);
	res = mono_mempool_alloc0 (image->mempool, size);
	mono_image_unlock (image);

	return res;
}

char*
mono_image_strdup (MonoImage *image, const char *s)
{
	char *res;

	mono_perfcounters->loader_bytes += strlen (s);
	mono_image_lock (image);
	res = mono_mempool_strdup (image->mempool, s);
	mono_image_unlock (image);

	return res;
}

GList*
g_list_prepend_image (MonoImage *image, GList *list, gpointer data)
{
	GList *new_list;
	
	new_list = mono_image_alloc (image, sizeof (GList));
	new_list->data = data;
	new_list->prev = list ? list->prev : NULL;
    new_list->next = list;

    if (new_list->prev)
            new_list->prev->next = new_list;
    if (list)
            list->prev = new_list;

	return new_list;
}

GSList*
g_slist_append_image (MonoImage *image, GSList *list, gpointer data)
{
	GSList *new_list;

	new_list = mono_image_alloc (image, sizeof (GSList));
	new_list->data = data;
	new_list->next = NULL;

	return g_slist_concat (list, new_list);
}

void
mono_image_lock (MonoImage *image)
{
	mono_locks_acquire (&image->lock, ImageDataLock);
}

void
mono_image_unlock (MonoImage *image)
{
	mono_locks_release (&image->lock, ImageDataLock);
}


/**
 * mono_image_property_lookup:
 *
 * Lookup a property on @image. Used to store very rare fields of MonoClass and MonoMethod.
 *
 * LOCKING: Takes the image lock
 */
gpointer 
mono_image_property_lookup (MonoImage *image, gpointer subject, guint32 property)
{
	gpointer res;

	mono_image_lock (image);
	res = mono_property_hash_lookup (image->property_hash, subject, property);
 	mono_image_unlock (image);

	return res;
}

/**
 * mono_image_property_insert:
 *
 * Insert a new property @property with value @value on @subject in @image. Used to store very rare fields of MonoClass and MonoMethod.
 *
 * LOCKING: Takes the image lock
 */
void
mono_image_property_insert (MonoImage *image, gpointer subject, guint32 property, gpointer value)
{
	mono_image_lock (image);
	mono_property_hash_insert (image->property_hash, subject, property, value);
 	mono_image_unlock (image);
}

/**
 * mono_image_property_remove:
 *
 * Remove all properties associated with @subject in @image. Used to store very rare fields of MonoClass and MonoMethod.
 *
 * LOCKING: Takes the image lock
 */
void
mono_image_property_remove (MonoImage *image, gpointer subject)
{
	mono_image_lock (image);
	mono_property_hash_remove_object (image->property_hash, subject);
 	mono_image_unlock (image);
}

