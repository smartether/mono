#ifndef __UNITY_MONO_UTILS_H
#define __UNITY_MONO_UTILS_H

#include <jni.h>
#include <glib.h>
#include <stdio.h>
#include <mono/metadata/object.h>

JNIEnv* gEnv;
char* gPkgNameC;
char* gFilesDirC;
GArray* gHotFilesC;

void mono_unity_Java_JNI_Pkg_Init(JNIEnv* env, jobject x, jint count);
void mono_unity_Java_JNI_Pkg_Set(JNIEnv* env, jobject x, jstring pkgName);
void mono_unity_Java_JNI_Pkg_SetFilesDir(JNIEnv* env, jobject x, jstring filesDir, jint len);
void mono_unity_Java_JNI_Pkg_SetFilesDirCstr(JNIEnv* env, jobject x, jcharArray filesDir, jint len);
void mono_unity_Java_JNI_Pkg_SetHotReloadFiles(JNIEnv* env, jobject x, jbyteArray fname, jint len);

/**
 *	Custom exit function, called instead of system exit()
 */
void unity_mono_exit( int code );

/**
 *	Redirects mono output where we want it.
 */
void unity_mono_redirect_output( const char *fout, const char *ferr );

/**
 *	Closes redirected output files.
 */
void unity_mono_close_output(void);

extern MonoString* mono_unity_get_embeddinghostname(void);

void mono_unity_write_to_unity_log(MonoString* str);

#ifdef WIN32
FILE* unity_fopen( const char *name, const char *mode );
#endif

extern gboolean mono_unity_socket_security_enabled_get (void);
extern void mono_unity_socket_security_enabled_set (gboolean enabled);
void mono_unity_set_vprintf_func(vprintf_func func);

void unity_mono_install_memory_callbacks(MonoMemoryCallbacks* callbacks);

gboolean
unity_mono_method_is_inflated (MonoMethod* method);

gboolean
unity_mono_method_is_generic (MonoMethod* method);

#endif
