#include <assert.h>
#include <errno.h>
#include "runtime_crt_file.h"

int main(void) {
    const char* path = "msvc-crt-modes.tmp";
    FILE* file = rt_crt_fopen(path, "wb");
    assert(file && fputs("a", file) >= 0 && fclose(file) == 0);
    file = rt_crt_fopen(path, "ab");
    assert(file && fputs("b", file) >= 0 && fclose(file) == 0);
    file = rt_crt_fopen(path, "r+b");
    assert(file && fgetc(file) == 'a' && fgetc(file) == 'b');
    assert(fseek(file, 0, SEEK_SET) == 0);
    assert(fputc('c', file) == 'c' && fclose(file) == 0);
    file = rt_crt_fopen(path, "rb");
    assert(file && fgetc(file) == 'c' && fgetc(file) == 'b' && fclose(file) == 0);
    errno = 0;
    assert(!rt_crt_fopen(path, "wbx") && errno == EEXIST);
    assert(remove(path) == 0);
    file = rt_crt_fopen(path, "wbx");
    assert(file && fputc('x', file) == 'x' && fclose(file) == 0);
    file = rt_crt_wfopen(L"msvc-crt-modes.tmp", L"wbx");
    assert(!file && errno == EEXIST);
    assert(remove(path) == 0);
    file = rt_crt_wfopen(L"msvc-crt-modes.tmp", L"wbx");
    assert(file && fclose(file) == 0 && remove(path) == 0);
    puts("runtime MSVC CRT file modes: PASS");
    return 0;
}
