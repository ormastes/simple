/* The shell driver supplies disposable fixtures and asserts marker absence. */
#import <Foundation/Foundation.h>
#import <Security/Security.h>
#include "../runtime_sosix_darwin_spawn_constraint_private.h"
#include <errno.h>
#include <assert.h>
#include <fcntl.h>
#include <stdio.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

int main(int argc, char **argv) { @autoreleasepool {
    if (argc != 10) return 70;
    /* argv: trusted launch operation mode main-marker dylib exe-marker lib-marker replacement */
    SecStaticCodeRef code = NULL; CFDictionaryRef information = NULL;
    NSURL *url = [NSURL fileURLWithPath:[NSString stringWithUTF8String:argv[1]]];
    OSStatus error = SecStaticCodeCreateWithPath((__bridge CFURLRef)url, 0, &code);
    if (!error) error = SecStaticCodeCheckValidity(code, kSecCSStrictValidate, NULL);
    if (!error) error = SecCodeCopySigningInformation(code, kSecCSSigningInformation, &information);
    if (error) { fprintf(stderr, "fixture signature rejected: %d\n", (int)error); if(code)CFRelease(code); return 71; }
    NSData *hash = ((__bridge NSDictionary *)information)[(__bridge NSString *)kSecCodeInfoUnique];
    if (hash.length != 20) return 72;
    unsigned char expected[20]; memcpy(expected, hash.bytes, sizeof(expected));
    CFRelease(information); CFRelease(code);
    int retained = -1;
    if (!strcmp(argv[3], "mutate")) { retained = open(argv[2], O_RDWR); if (retained < 0) return 73; }
    posix_spawnattr_t attributes;
    SosixDarwinSpawnConstraint storage;
    if (posix_spawnattr_init(&attributes)) return 74;
    assert(sosix_darwin_spawn_constraint_attach(NULL, expected, 20, &storage) == EINVAL);
    assert(sosix_darwin_spawn_constraint_attach(&attributes, NULL, 20, &storage) == EINVAL);
    assert(sosix_darwin_spawn_constraint_attach(&attributes, expected, 19, &storage) == EINVAL);
    assert(sosix_darwin_spawn_constraint_attach(&attributes, expected, 20, NULL) == EINVAL);
    if (strcmp(argv[3], "unbound")) {
        int result = sosix_darwin_spawn_constraint_attach(&attributes, expected, sizeof(expected), &storage);
        if (result) { fprintf(stderr, "constraint unavailable: %d\n", result); return 78; }
    }
    /* Deterministic adversary acts after all identity setup, before kernel lookup. */
    if (!strcmp(argv[3], "replace") && rename(argv[9], argv[2])) return 75;
    if (retained >= 0) {
        struct stat st; if (fstat(retained, &st)) return 76;
        char *bytes = malloc((size_t)st.st_size); if (!bytes) return 76;
        if (pread(retained, bytes, (size_t)st.st_size, 0) != st.st_size) return 76;
        const char needle[] = "SOSIX_SIGNED_PAYLOAD_7aafe2c1";
        off_t offset = -1;
        for (off_t i=0; i+(off_t)sizeof(needle)<=st.st_size; ++i)
            if (!memcmp(bytes+i, needle, sizeof(needle))) { offset=i; break; }
        free(bytes);
        if (offset < 0 || pwrite(retained, "X", 1, offset) != 1) return 76;
        close(retained);
    }
    char executable_env[4096], library_env[4096], injection_env[4096];
    int written = snprintf(executable_env,sizeof(executable_env),"SOSIX_EXECUTABLE_MARKER=%s",argv[7]);
    if (written < 0 || (size_t)written >= sizeof(executable_env)) return 77;
    written = snprintf(library_env,sizeof(library_env),"SOSIX_LIBRARY_MARKER=%s",argv[8]);
    if (written < 0 || (size_t)written >= sizeof(library_env)) return 77;
    written = snprintf(injection_env,sizeof(injection_env),"DYLD_INSERT_LIBRARIES=%s",argv[6]);
    if (written < 0 || (size_t)written >= sizeof(injection_env)) return 77;
    char *environment[] = {executable_env,library_env,NULL,NULL};
    if (!strcmp(argv[4],"inject")) environment[2] = injection_env;
    char *arguments[] = {argv[2],argv[4],argv[5],argv[6],NULL};
    pid_t pid = -1;
    int result = posix_spawn(&pid,argv[2],NULL,&attributes,arguments,environment);
    posix_spawnattr_destroy(&attributes);
    if (result) { fprintf(stderr,"spawn rejected: %d\n",result); return 79; }
    int status; pid_t reaped;
    do reaped=waitpid(pid,&status,0); while(reaped<0 && errno==EINTR);
    if (reaped != pid) return 80;
    if (WIFEXITED(status)) return WEXITSTATUS(status);
    if (WIFSIGNALED(status)) return 128+WTERMSIG(status);
    return 81;
} }
