#include "runtime.h"

#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

static void require(int condition, const char* message) {
    if (!condition) {
        fprintf(stderr, "FAIL: %s\n", message);
        exit(1);
    }
}

int main(void) {
    char root[] = "/tmp/simple-dir-sync-XXXXXX";
    require(mkdtemp(root) != NULL, "mkdtemp");
    size_t root_len = strlen(root);
    require(rt_dir_sync(root, (int64_t)root_len) == 1, "directory sync succeeds");

    char file_path[sizeof(root) + 8];
    snprintf(file_path, sizeof(file_path), "%s/file", root);
    int file = open(file_path, O_CREAT | O_WRONLY, 0600);
    require(file >= 0, "create ordinary file");
    require(close(file) == 0, "close ordinary file");
    require(rt_dir_sync(file_path, (int64_t)strlen(file_path)) == 0,
            "ordinary file is rejected");
    require(rt_dir_sync("/tmp/simple-dir-sync-missing", 28) == 0,
            "missing directory is rejected");
    require(rt_dir_sync(NULL, 1) == 0, "null pointer is rejected");
    require(rt_dir_sync(root, 0) == 0, "zero length is rejected");

    char embedded_nul[] = {'/', 't', 'm', 'p', '\0', 'x'};
    require(rt_dir_sync(embedded_nul, 6) == 0, "embedded NUL is rejected");

    require(unlink(file_path) == 0, "remove ordinary file");
    require(rmdir(root) == 0, "remove test directory");
    puts("PASS: rt_dir_sync ABI and POSIX behavior");
    return 0;
}
