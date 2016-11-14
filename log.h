#ifndef _LOG_H
#define _LOG_H
#ifdef _ENABLE_LOG
#define LOG_TAG "unity"
#undef LOG
#include <android/log.h>
#define LOGD(...)__android_log_print(ANDROID_LOG_DEBUG,LOG_TAG,__VA_ARGS__)

#else

//void __Empty__(){
	
//}

#define LOGD(...){}//__Empty__()

#endif

#endif
