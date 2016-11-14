#include <jni.h>
#include "../log.h"
#include "unity_utils.h"
#include <stdio.h>
#include <stdlib.h>
#ifdef WIN32
#include <fcntl.h>
#endif
#include <mono/metadata/object.h>
#include <mono/metadata/metadata.h>
#include <mono/metadata/tabledefs.h>
#include <mono/metadata/class-internals.h>
#include <mono/metadata/object-internals.h>
#include <mono/metadata/metadata-internals.h>
#include <mono/metadata/threads.h>
#include <mono/metadata/tokentype.h>
#include <mono/utils/mono-string.h>

#include <glib.h>

#ifdef WIN32
#define UTF8_2_WIDE(src,dst) MultiByteToWideChar( CP_UTF8, 0, src, -1, dst, MAX_PATH )
#endif

#undef exit

void unity_mono_exit( int code )
{
	//fprintf( stderr, "mono: exit called, code %d\n", code );
	exit( code );
}

#ifdef WIN32

HANDLE unity_log_output = 0;

void unity_mono_redirect_output( HANDLE handle )
{
	int fd;
	DWORD written;
//	int fd_copy;
	unity_log_output = handle;	
	fd = _open_osfhandle((intptr_t)handle, (_O_APPEND | _O_TEXT));
	stdout->_file = fd;
	_dup2(fd,_fileno(stdout));
	//*stdout = *_fdopen(fd, "at");
	
	setvbuf(stdout, NULL, _IONBF, 0);
	
	//fprintf(stdout, "printf from mono\n");
	//WriteFile(handle,"WriteFile from mono",16,&written,NULL);
}

HANDLE unity_mono_get_log_handle()
{
	return unity_log_output;
}

void unity_mono_close_output()
{
	fclose( stdout );
	fclose( stderr );
}

FILE* unity_fopen( const char *name, const char *mode )
{
	wchar_t wideName[MAX_PATH];
	wchar_t wideMode[MAX_PATH];
	UTF8_2_WIDE(name, wideName);
	UTF8_2_WIDE(mode, wideMode);
	return _wfopen( wideName, wideMode );
}

extern LONG CALLBACK seh_vectored_exception_handler(EXCEPTION_POINTERS* ep);
LONG mono_unity_seh_handler(EXCEPTION_POINTERS* ep)
{
#if defined(TARGET_X86) || defined(TARGET_AMD64)
	return seh_vectored_exception_handler(ep);
#else
	g_assert_not_reached();
#endif
}

int (*gUnhandledExceptionHandler)(EXCEPTION_POINTERS*) = NULL;

void mono_unity_set_unhandled_exception_handler(void* handler)
{
	gUnhandledExceptionHandler = handler;
}

#endif //Win32

GString* gEmbeddingHostName = 0;


void mono_unity_write_to_unity_log(MonoString* str)
{
	fprintf(stdout, mono_string_to_utf8(str));
	fflush(stdout);
}


void mono_unity_set_embeddinghostname(const char* name)
{
	gEmbeddingHostName = g_string_new(name);
}



MonoString* mono_unity_get_embeddinghostname()
{
	if (gEmbeddingHostName == 0)
		mono_unity_set_embeddinghostname("mono");
	return mono_string_new_wrapper(gEmbeddingHostName->str);
}

static gboolean socket_security_enabled = FALSE;

gboolean
mono_unity_socket_security_enabled_get ()
{
	return socket_security_enabled;
}

void
mono_unity_socket_security_enabled_set (gboolean enabled)
{
	socket_security_enabled = enabled;
}

void mono_unity_set_vprintf_func (vprintf_func func)
{
	set_vprintf_func (func);
}

gboolean
mono_unity_class_is_interface (MonoClass* klass)
{
	return MONO_CLASS_IS_INTERFACE(klass);
}

gboolean
mono_unity_class_is_abstract (MonoClass* klass)
{
	return (klass->flags & TYPE_ATTRIBUTE_ABSTRACT);
}

void
unity_mono_install_memory_callbacks(MonoMemoryCallbacks* callbacks)
{
	g_mem_set_callbacks (callbacks);
}

void mono_unity_thread_clear_domain_fields (void)
{
	/*
	 we need to clear fields that may reference objects living in non-root appdomain
	 since the objects will live but their vtables will be destroyed when domain is torn down.
	 */
	MonoThread* thread = mono_thread_current ();
	thread->principal = NULL;
}

// classes_ref is a preallocated array of *length_ref MonoClass*
// returned classes are stored in classes_ref, number of stored classes is stored in length_ref
// return value is number of classes found (which may be greater than number of classes stored)
unsigned mono_unity_get_all_classes_with_name_case (MonoImage *image, const char *name, MonoClass **classes_ref, unsigned *length_ref)
{
	MonoClass *klass;
	MonoTableInfo *tdef = &image->tables [MONO_TABLE_TYPEDEF];
	int i, count;
	guint32 attrs, visibility;
	unsigned length = 0;

	/* (yoinked from icall.c) we start the count from 1 because we skip the special type <Module> */
	for (i = 1; i < tdef->rows; ++i)
	{
		klass = mono_class_get (image, (i + 1) | MONO_TOKEN_TYPE_DEF);
		if (klass && klass->name && 0 == mono_utf8_strcasecmp (klass->name, name))
		{
			if (length < *length_ref)
				classes_ref[length] = klass;
			++length;
		}
	}

	if (length < *length_ref)
		*length_ref = length;
	return length;
}

gboolean
unity_mono_method_is_inflated (MonoMethod* method)
{
	return method->is_inflated;
}

gboolean
unity_mono_method_is_generic (MonoMethod* method)
{
	return method->is_generic;
}

/********** JNI Interface   ************/
//static JNIEnv* gEnv;
//static char* gPkgNameC;
//static char* gFilesDirC;


void mono_unity_Java_JNI_Pkg_Set(JNIEnv* env, jobject x, jstring pkgName){
        gEnv = env;
        jboolean isCopy = 0;
        gPkgNameC = (*env)->GetStringUTFChars(env, pkgName, &isCopy);
	LOGD("$$ set package name as %s", gPkgNameC);
}

void mono_unity_Java_JNI_Pkg_SetFilesDir(JNIEnv* env, jobject x, jstring filesDir, jint len){
        jboolean isCopy = 0;
	gFilesDirC = g_try_malloc(len);
        char* inStr = (*env)->GetStringUTFChars(env, filesDir, &isCopy);
	memcpy(gFilesDirC, inStr, len);
	LOGD("$$ set fileDir as %s", gFilesDirC);
}

void mono_unity_Java_JNI_Pkg_SetFilesDirCstr(JNIEnv* env, jobject x, jbyteArray filesDir, jint len){
	jboolean isCopy = 0;
	gFilesDirC = g_try_malloc(len+1);
	memset(gFilesDirC, '\0', len+1);
        char* inStr  = (char*)(*env)->GetByteArrayElements(env, filesDir, &isCopy);
	memcpy(gFilesDirC, inStr, len);
	LOGD("$$ set fileDIrCstr as %s", gFilesDirC);
}

void mono_unity_Java_JNI_Pkg_Init(JNIEnv* env, jobject x, jint count){
        if(gHotFilesC!=NULL){
	  g_free(gHotFilesC);
	  gHotFilesC = NULL;
//	  gboolean false = 0;
//	  gboolean true = 1;
	}
        gHotFilesC = g_array_new(FALSE,FALSE, sizeof(char*));
        

}

jint JNI_OnLoad(JavaVM* vm, void* reserved){
	gHotFilesC = g_array_new(FALSE,FALSE, sizeof(char*));
        gFilesDirC = g_try_malloc(1);
        memset(gFilesDirC, '\0', 1);

//        JNIEnv* env;
//       if (vm->GetEnv(reinterpret_cast<void**>(&env), JNI_VERSION_1_6) != JNI_OK) {
//    	    return -1;
//        }
	return JNI_VERSION_1_6;
}

void mono_unity_Java_JNI_Pkg_SetHotReloadFiles(JNIEnv* env, jobject x, jbyteArray fname, jint len){
	if(gHotFilesC!=NULL){
	  char* name = g_try_malloc(len+1);
	  memset(name,'\0',len+1);
	  jboolean isCopy = 0;
	  char* inStr = (char*)(*env)->GetByteArrayElements(env, fname, &isCopy);
	  memcpy(name, inStr, len);
	  g_array_append_val(gHotFilesC, name);
	  //g_array_append_vals(gHotFilesC, name, len); 
	}
}
