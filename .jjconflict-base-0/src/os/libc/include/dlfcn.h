#ifndef SIMPLEOS_DLFCN_H
#define SIMPLEOS_DLFCN_H

#define RTLD_LAZY   0x00001
#define RTLD_NOW    0x00002
#define RTLD_GLOBAL 0x00100
#define RTLD_LOCAL  0x00000

#ifndef NULL
#define NULL ((void *)0)
#endif

#define RTLD_DEFAULT ((void *)0)
#define RTLD_NEXT    ((void *)-1)

#ifdef __cplusplus
extern "C" {
#endif

void *dlopen(const char *path, int mode);
void *dlsym(void *handle, const char *name);
int   dlclose(void *handle);
char *dlerror(void);

#ifdef __cplusplus
}
#endif
#endif
