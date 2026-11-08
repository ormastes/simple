#include <assert.h>
#include <errno.h>
#include <sys/stat.h>
#include "runtime_crt_file.h"

int main(void) {
    const char* path = "msvc-crt-descriptor.tmp";
    int fd = rt_crt_open(path, _O_CREAT | _O_TRUNC | _O_RDWR | _O_BINARY,
                         _S_IREAD | _S_IWRITE);
    assert(fd >= 0);
    assert(rt_crt_write(fd, "abc", 3) == 3);
    assert(_lseek(fd, 0, SEEK_SET) == 0);
    char buffer[4] = {0};
    assert(rt_crt_read(fd, buffer, 3) == 3);
    assert(strcmp(buffer, "abc") == 0);
    int second = rt_crt_open(path, _O_RDONLY | _O_BINARY);
    assert(second >= 0); /* Open retains the previous deny-none sharing. */
    assert(rt_crt_close(second) == 0);
    assert(rt_crt_close(fd) == 0);
    errno = 0;
    assert(rt_crt_open(path, _O_CREAT | _O_EXCL | _O_WRONLY,
                       _S_IREAD | _S_IWRITE) == -1 && errno == EEXIST);
    FILE* file = rt_crt_fopen(path, "rb");
    assert(file && fgetc(file) == 'a');
    FILE* shared = rt_crt_fopen(path, "rb");
    assert(shared);
    assert(fclose(shared) == 0 && fclose(file) == 0);
    file = rt_crt_wfopen(L"msvc-crt-descriptor.tmp", L"rb");
    assert(file && fgetc(file) == 'a' && fclose(file) == 0);
    assert(rt_crt_unlink(path) == 0);
    fd = rt_crt_open(path, _O_CREAT | _O_RDWR | _O_BINARY, 0666);
    assert(fd >= 0 && rt_crt_close(fd) == 0);
    assert(rt_crt_unlink(path) == 0);
    errno = 0;
    assert(rt_crt_open(path, _O_RDONLY) == -1 && errno == ENOENT);
    assert(!rt_crt_fopen(path, "rb"));
    assert(_mkdir("msvc-crt-directory.tmp") == 0);
    assert(rt_crt_rmdir("msvc-crt-directory.tmp") == 0);
    puts("runtime MSVC CRT files: PASS");
    return 0;
}
