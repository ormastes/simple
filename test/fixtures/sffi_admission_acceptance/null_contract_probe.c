#include <dlfcn.h>
#include <stdio.h>

typedef int (*create_fn)(void **out_handle);

int main(int argc, char **argv) {
    if (argc != 2) return 2;
    void *library = dlopen(argv[1], RTLD_NOW | RTLD_LOCAL);
    if (library == NULL) return 2;
    create_fn create = (create_fn)dlsym(library, "rt_sffi_acceptance_create");
    if (create == NULL) {
        dlclose(library);
        return 2;
    }
    void *out_handle = (void *)1;
    int status = create(&out_handle);
    dlclose(library);
    if (status == 0 && out_handle == NULL) {
        puts("E-SFFI-ADM-NULL-CONTRACT");
        return 1;
    }
    return 2;
}
