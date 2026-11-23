#include <windows.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <stdbool.h>

extern uint64_t rt_array_new(uint64_t);
extern bool rt_array_push(uint64_t, uint64_t);
extern uint64_t rt_string_new(const unsigned char *, uint64_t);
extern const char *rt_string_data(uint64_t);
extern int64_t rt_string_len(uint64_t);
extern int64_t *rt_process_run_bounded_tuple(const char *, uint64_t, uint64_t, int64_t, int64_t);

static void arg(uint64_t args, const char *text) {
    rt_array_push(args, rt_string_new((const unsigned char *)text, strlen(text)));
}

int main(int argc, char **argv) {
    if (argc > 1 && !strcmp(argv[1], "normal")) {
        puts("bounded-provider-ok");
        return 0;
    }
    if (argc > 2 && !strcmp(argv[1], "sleep")) {
        FILE *pidfile = fopen(argv[2], "w");
        if (!pidfile) return 10;
        fprintf(pidfile, "%lu\n", (unsigned long)GetCurrentProcessId());
        fclose(pidfile);
        Sleep(30000);
        return 11;
    }
    char self[MAX_PATH];
    if (!GetModuleFileNameA(NULL, self, sizeof self)) return 12;
    uint64_t args = rt_array_new(1);
    arg(args, "normal");
    ULONGLONG start = GetTickCount64();
    int64_t *result = rt_process_run_bounded_tuple(self, strlen(self), args, 5000, 65536);
    if (!result || result[2] != 0 || GetTickCount64() - start > 7000) return 20;
    const char *out = rt_string_data((uint64_t)result[0]);
    int64_t len = rt_string_len((uint64_t)result[0]);
    if (!out || !((len == 20 && !memcmp(out, "bounded-provider-ok\n", 20)) ||
                  (len == 21 && !memcmp(out, "bounded-provider-ok\r\n", 21)))) return 21;
    puts("normal=PASS");
    const char *pidpath = "bounded-provider-child.pid";
    DeleteFileA(pidpath);
    args = rt_array_new(2);
    arg(args, "sleep"); arg(args, pidpath);
    start = GetTickCount64();
    result = rt_process_run_bounded_tuple(self, strlen(self), args, 1000, 65536);
    ULONGLONG elapsed = GetTickCount64() - start;
    /* Rust bounded capture retains its (-1, stderr TIMEOUT) contract. */
    if (!result || result[2] != -1 || elapsed < 900 || elapsed > 7000) return 30;
    const char *error = rt_string_data((uint64_t)result[1]);
    int64_t error_len = rt_string_len((uint64_t)result[1]);
    if (!error || error_len < 9 || memcmp(error + error_len - 9, "\nTIMEOUT\n", 9)) return 34;
    FILE *pidfile = fopen(pidpath, "r");
    unsigned long pid = 0;
    if (!pidfile || fscanf(pidfile, "%lu", &pid) != 1 || !pid) return 31;
    fclose(pidfile);
    HANDLE child = OpenProcess(SYNCHRONIZE | PROCESS_QUERY_LIMITED_INFORMATION, FALSE, (DWORD)pid);
    if (child) {
        DWORD wait = WaitForSingleObject(child, 0);
        CloseHandle(child);
        if (wait != WAIT_OBJECT_0) return 32;
    } else if (GetLastError() != ERROR_INVALID_PARAMETER) return 33;
    printf("timeout=PASS elapsed_ms=%llu child_quiescent=1\n", (unsigned long long)elapsed);
    return 0;
}
