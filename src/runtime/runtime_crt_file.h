#ifndef SIMPLE_RUNTIME_CRT_FILE_H
#define SIMPLE_RUNTIME_CRT_FILE_H
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#if defined(_MSC_VER)
#include <stdarg.h>
#include <fcntl.h>
#include <io.h>
#include <direct.h>
#include <share.h>
static int rt_crt_open(const char* path, int flags, ...) {
    int mode = 0;
    if (flags & _O_CREAT) {
        va_list args;
        va_start(args, flags);
        mode = va_arg(args, int);
        va_end(args);
        /* Legacy _open ignores POSIX group/other permission bits. Secure
         * _sopen_s rejects them instead; retain the legacy owner bits. */
        mode &= _S_IREAD | _S_IWRITE;
    }
    int fd = -1;
    return _sopen_s(&fd, path, flags, _SH_DENYNO, mode) == 0 ? fd : -1;
}
static FILE* rt_crt_fopen(const char* path, const char* mode) {
    return _fsopen(path, mode, _SH_DENYNO);
}
static int rt_crt_wopen(const wchar_t* path, int flags, int mode) {
    int fd = -1;
    mode &= _S_IREAD | _S_IWRITE;
    return _wsopen_s(&fd, path, flags, _SH_DENYNO, mode) == 0 ? fd : -1;
}
static FILE* rt_crt_wfopen(const wchar_t* path, const wchar_t* mode) {
    return _wfsopen(path, mode, _SH_DENYNO);
}
#define rt_crt_rmdir _rmdir
#define rt_crt_unlink _unlink
#define rt_crt_read _read
#define rt_crt_write _write
#define rt_crt_close _close
#else
#define rt_crt_open open
#define rt_crt_wopen _wopen
#define rt_crt_fopen fopen
#define rt_crt_wfopen _wfopen
#define rt_crt_rmdir rmdir
#define rt_crt_unlink unlink
#define rt_crt_read read
#define rt_crt_write write
#define rt_crt_close close
#endif
#endif
