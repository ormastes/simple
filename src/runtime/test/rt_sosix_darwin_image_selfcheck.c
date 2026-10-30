#include "../runtime_sosix_darwin_image_private.h"
#include <assert.h>
#include <stdio.h>
#include <sys/wait.h>
#include <mach-o/dyld.h>
int main(int argc, char **args) {
    if (argc > 1 && strcmp(args[1], "child") == 0) return 0;
    char path[PATH_MAX]; uint32_t size = sizeof(path); assert(_NSGetExecutablePath(path, &size) == 0);
    int original = open(path, O_RDONLY | O_CLOEXEC); assert(original >= 0);
    char source_path[] = "/tmp/sosix-source-XXXXXXXX"; int source = mkstemp(source_path); assert(source >= 0);
    char bytes[65536]; ssize_t n;
    while ((n = read(original, bytes, sizeof(bytes))) > 0) assert(write(source, bytes, (size_t)n) == n);
    assert(n == 0); close(original);
    int fd = source;
    SosixDarwinImage image;
    assert(sosix_darwin_image_create(fd, &image) == 0);
    assert(pwrite(fd, "X", 1, 0) == 1); close(fd); unlink(source_path);
    assert(image.generation != 0);
    pid_t pid = -1;
    char *argv[] = {"image", "child", NULL};
    char *env[] = {"PATH=/usr/bin:/bin", NULL};
    assert(sosix_darwin_image_spawn(&image, image.generation + 1, &pid, NULL, NULL, argv, env) == ESTALE);
    assert(sosix_darwin_image_spawn(&image, image.generation, &pid, NULL, NULL, argv, env) == 0);
    int status; assert(waitpid(pid, &status, 0) == pid); assert(WIFEXITED(status) && WEXITSTATUS(status) == 0);
    assert(chmod(image.path, 0700) == 0);
    int corrupt = open(image.path, O_WRONLY); assert(corrupt >= 0);
    assert(pwrite(corrupt, "X", 1, 0) == 1); close(corrupt);
    assert(sosix_darwin_image_spawn(&image, image.generation, &pid, NULL, NULL, argv, env) == ESTALE);
    uint64_t generation = image.generation;
    assert(sosix_darwin_image_close(&image, generation) == 0);
    assert(sosix_darwin_image_close(&image, generation) == ESTALE);
    puts("darwin image owner selfcheck passed");
}
