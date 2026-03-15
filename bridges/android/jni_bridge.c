// jni_bridge.c — JNI glue between Android Java and Simple runtime
//
// Converts Java String[] args to C argc/argv and calls simple_app_main().
//
// Build with Android NDK:
//   $NDK/toolchains/llvm/prebuilt/linux-x86_64/bin/aarch64-linux-android21-clang \
//     -shared -o libsimple_app.so jni_bridge.c -lsimple_runtime

#include <jni.h>
#include <string.h>
#include <stdlib.h>

// Exported by the Simple runtime/app
extern int simple_app_main(int argc, char** argv);

JNIEXPORT jint JNICALL
Java_simple_SimpleActivity_nativeAppMain(JNIEnv* env, jobject thiz, jobjectArray args) {
    // Convert Java String[] to C char**
    int argc = (*env)->GetArrayLength(env, args);
    char** argv = (char**)malloc(sizeof(char*) * (argc + 1));
    if (!argv) return -1;

    for (int i = 0; i < argc; i++) {
        jstring jstr = (jstring)(*env)->GetObjectArrayElement(env, args, i);
        const char* str = (*env)->GetStringUTFChars(env, jstr, NULL);
        argv[i] = strdup(str);
        (*env)->ReleaseStringUTFChars(env, jstr, str);
        (*env)->DeleteLocalRef(env, jstr);
    }
    argv[argc] = NULL;

    // Call Simple app entry point
    int result = simple_app_main(argc, argv);

    // Clean up
    for (int i = 0; i < argc; i++) {
        free(argv[i]);
    }
    free(argv);

    return result;
}
