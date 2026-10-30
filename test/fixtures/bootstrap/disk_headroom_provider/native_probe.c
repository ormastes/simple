/* Link this probe against genuine Rust058 + runtime_disk_headroom.o, then
 * against the canonical full-C profile separately. No replacement text ABI. */
#include "runtime.h"
#include "runtime_disk_headroom_private.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#if defined(_WIN32)
#include <windows.h>
#else
#include <sys/statvfs.h>
#include <sys/stat.h>
#include <unistd.h>
#endif
static unsigned checks;
static void checked(int ok) { ++checks; if (!ok) { fprintf(stderr, "disk-headroom check=%u failed\n", checks); exit(1); } }
static int64_t text(const char *s, size_t len) { return rt_string_new_literal((const uint8_t *)s, len); }
static int64_t query(const char *s) { int64_t v=text(s,strlen(s)); int64_t n=rt_host_disk_headroom_bytes_v1(v); rt_string_free(v); return n; }
#if defined(_WIN32)
static int wide(const char *s, WCHAR out[4096]) { return MultiByteToWideChar(CP_UTF8,MB_ERR_INVALID_CHARS,s,-1,out,4096); }
#endif
int main(int argc, char **argv) {
    if (argc != 2) return 2;
    const char *root=argv[1];
    int64_t oracle;
#if defined(_WIN32)
    WCHAR root_w[4096]; ULARGE_INTEGER available={0};
    if (!wide(root,root_w) || !GetDiskFreeSpaceExW(root_w,&available,NULL,NULL)) return 2;
    oracle=rt_disk_headroom_product_v1(available.QuadPart,1);
    unsigned long pid=GetCurrentProcessId();
#else
    struct statvfs info; if (statvfs(root,&info)) return 2;
    oracle=rt_disk_headroom_product_v1(info.f_bavail,info.f_frsize);
    unsigned long pid=(unsigned long)getpid();
#endif
    checked(oracle > 3);
    int64_t actual=query(root); checked(actual > 3);
    checked(actual >= oracle-67108864 && (oracle > INT64_MAX-67108864 || actual <= oracle+67108864));
    checked(query("") == 0);
    char missing[4096]; snprintf(missing,sizeof(missing),"%s/headroom-missing-%lu/no-such-volume",root,pid);
    checked(query(missing) == 0);
    const char embedded[]=".\0not-a-path"; int64_t v=text(embedded,sizeof(embedded)-1);
    checked(rt_host_disk_headroom_bytes_v1(v)==0); rt_string_free(v);
    checked(rt_host_disk_headroom_bytes_v1(rt_value_nil())==0);
    checked(rt_host_disk_headroom_bytes_v1(rt_value_int(7))==0);
    /* Windows rejects malformed UTF-8; POSIX probes an absent native-byte name. */
    const char invalid_utf8[]={(char)0xff,0}; checked(query(invalid_utf8)==0);
    char oversized[4096]; memset(oversized,'a',sizeof(oversized));
    v=text(oversized,sizeof(oversized)); checked(rt_host_disk_headroom_bytes_v1(v)==0); rt_string_free(v);
    char unicode[4096]; snprintf(unicode,sizeof(unicode),"%s/headroom space-%lu-\xce\xbb-\xe4\xb8\xad",root,pid);
#if defined(_WIN32)
    WCHAR unicode_w[4096]; if (!wide(unicode,unicode_w) || !CreateDirectoryW(unicode_w,NULL)) return 2;
    int64_t unicode_free=query(unicode); int cleaned=RemoveDirectoryW(unicode_w);
#else
    if (mkdir(unicode,0700)) return 2;
    int64_t unicode_free=query(unicode); int cleaned=(rmdir(unicode)==0);
#endif
    checked(cleaned && unicode_free > 3);
    checked(rt_disk_headroom_product_v1(UINT64_MAX,4096)==INT64_MAX);
    checked(rt_disk_headroom_product_v1(0,UINT64_MAX)==0);
    checked(rt_disk_headroom_product_v1(17,4096)==69632);
    printf("disk-headroom-provider assertions=%u\n",checks);
    return 0;
}
