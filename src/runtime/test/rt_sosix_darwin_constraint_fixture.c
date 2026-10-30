#include <dlfcn.h>
#include <fcntl.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

static void mark(const char *path) {
    if (!path || !*path) return;
    int fd = open(path, O_WRONLY | O_CREAT | O_EXCL, 0600);
    if (fd >= 0) { (void)write(fd, "entered\n", 8); close(fd); }
}

#ifdef SOSIX_LIBRARY_FIXTURE
#ifndef SOSIX_FIXTURE_SYMBOL
#define SOSIX_FIXTURE_SYMBOL sosix_fixture_value
#endif
__attribute__((constructor)) static void library_constructor(void) {
    mark(getenv("SOSIX_LIBRARY_MARKER"));
}
#ifdef SOSIX_TRANSITIVE_FIXTURE
extern int sosix_leaf_value(void);
int SOSIX_FIXTURE_SYMBOL(void) { return sosix_leaf_value() == 99 ? SOSIX_LIBRARY_FIXTURE : 98; }
#else
int SOSIX_FIXTURE_SYMBOL(void) { return SOSIX_LIBRARY_FIXTURE; }
#endif
#else
/* A signed constant page used by the retained-descriptor mutation test. */
const char sosix_signed_payload[] = "SOSIX_SIGNED_PAYLOAD_7aafe2c1";
__attribute__((constructor)) static void executable_constructor(void) {
    mark(getenv("SOSIX_EXECUTABLE_MARKER"));
}
int main(int argc, char **argv) {
    if (argc < 3) return 2;
    mark(argv[2]);
    if (!strcmp(argv[1], "dlopen")) {
        if (argc != 4) return 3;
        void *library = dlopen(argv[3], RTLD_NOW | RTLD_LOCAL);
        if (!library) return 42;
        int (*value)(void) = dlsym(library, "sosix_fixture_value");
        return value && value() == 17 ? 0 : 43;
    }
    return sosix_signed_payload[0] == 'S' ? 0 : 44;
}
#endif
