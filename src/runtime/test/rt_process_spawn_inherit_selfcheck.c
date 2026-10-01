/* Isolated core-C spawn/wait test. Build this executable beside the matching
 * .cmd fixture and inspect both stdout and stderr. The parent supplies its
 * own stdin pipe so timeout and child input do not depend on a shell pipe.
 * Copy rt_process_spawn_inherit_selfcheck.cmd as simple_mcp_server.cmd beside
 * the executable, named selfcheck.exe. */
#include "runtime.h"
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <wchar.h>
#include <windows.h>

/* Other exports from runtime_process.c remain in this standalone link. Any
 * unexpected route through them must fail rather than act as a test stub. */
SplArray* rt_array_new(int64_t cap) { (void)cap; abort(); }
int64_t rt_array_len(SplArray* array) { (void)array; abort(); }
int64_t rt_array_get(SplArray* array, int64_t idx) { (void)array; (void)idx; abort(); }
int8_t rt_array_push(SplArray* array, int64_t value) { (void)array; (void)value; abort(); }
int64_t rt_string_new(const uint8_t* bytes, uint64_t len) { (void)bytes; (void)len; abort(); }
const uint8_t* rt_string_data(int64_t string) { (void)string; abort(); }
int64_t rt_value_int(int64_t value) { (void)value; abort(); }

static bool fixture_path(wchar_t* path, size_t capacity) {
    DWORD length = GetModuleFileNameW(NULL, path, (DWORD)capacity);
    if (length == 0 || length >= capacity) return false;
    wchar_t* slash = wcsrchr(path, L'\\');
    if (!slash) return false;
    return swprintf(slash + 1, capacity - (size_t)(slash + 1 - path),
                    L"simple_mcp_server.cmd") > 0;
}

static int child_mode(void) {
    if (GetEnvironmentVariableW(L"_SIMPLE_STACK_SET", NULL, 0) != 0) return 91;
    wchar_t expected[32768], route[32768];
    if (!fixture_path(expected, sizeof(expected) / sizeof(expected[0]))) return 92;
    DWORD route_length = GetEnvironmentVariableW(L"_SIMPLE_MCP_WRAPPER_PATH",
        route, (DWORD)(sizeof(route) / sizeof(route[0])));
    if (route_length == 0 || route_length >= sizeof(route) / sizeof(route[0]) ||
        wcscmp(expected, route) != 0) return 93;
    wchar_t number[40];
    if (!GetEnvironmentVariableW(L"_SIMPLE_MCP_TEST_SENTINEL_HANDLE", number, 40)) return 94;
    HANDLE sentinel = (HANDLE)(uintptr_t)_wcstoui64(number, NULL, 10);
    DWORD flags = 0;
    if (GetHandleInformation(sentinel, &flags)) return 95;
    if (GetEnvironmentVariableW(L"_SIMPLE_MCP_TEST_NEGATIVE", NULL, 0)) return -42;
    Sleep(150);
    char line[100];
    if (!fgets(line, sizeof(line), stdin)) return 96;
    printf("child:%s", line);
    fflush(stdout);
    fprintf(stderr, "child-stderr\n");
    return 37;
}

int main(int argc, char** argv) {
    if (argc > 1 && strcmp(argv[1], "--child") == 0) return child_mode();
    SECURITY_ATTRIBUTES security = {sizeof(security), NULL, TRUE};
    HANDLE sentinel = CreateEventW(&security, TRUE, FALSE, NULL);
    if (!sentinel) return 1;
    wchar_t number[40];
    swprintf(number, 40, L"%llu", (unsigned long long)(uintptr_t)sentinel);
    SetEnvironmentVariableW(L"_SIMPLE_MCP_TEST_SENTINEL_HANDLE", number);
    SetEnvironmentVariableW(L"_SIMPLE_STACK_SET", L"parent-marker");
    SetEnvironmentVariableW(L"_SIMPLE_MCP_WRAPPER_PATH", L"C:\\spoof.cmd");

    SECURITY_ATTRIBUTES pipe_security = {sizeof(pipe_security), NULL, TRUE};
    HANDLE input_read = NULL, input_write = NULL;
    if (!CreatePipe(&input_read, &input_write, &pipe_security, 0)) return 12;
    if (!SetHandleInformation(input_write, HANDLE_FLAG_INHERIT, 0)) return 13;
    HANDLE original_input = GetStdHandle(STD_INPUT_HANDLE);
    if (!SetStdHandle(STD_INPUT_HANDLE, input_read)) return 14;
    int64_t pid = rt_process_spawn_inherit();
    SetStdHandle(STD_INPUT_HANDLE, original_input);
    CloseHandle(input_read);
    if (pid <= 0) return 2;
    int64_t timed = rt_process_wait(pid, 1);
    if (timed != -2) {
        fprintf(stderr, "expected timeout, got %lld\n", (long long)timed);
        return 2;
    }
    DWORD sent = 0;
    if (!WriteFile(input_write, "hello\n", 6, &sent, NULL) || sent != 6) return 15;
    CloseHandle(input_write);
    int64_t normal = rt_process_wait(pid, 0);
    DWORD normal_last_error = GetLastError();
    if (normal != 37) {
        fprintf(stderr, "normal child status=%lld GetLastError=%lu\n",
                (long long)normal, (unsigned long)normal_last_error);
        return 3;
    }
    if (rt_process_wait(pid, 0) != -1 || rt_process_wait(-1, 0) != -1) return 4;

    wchar_t value[100];
    if (!GetEnvironmentVariableW(L"_SIMPLE_STACK_SET", value, 100) ||
        wcscmp(value, L"parent-marker") != 0) return 5;
    if (!GetEnvironmentVariableW(L"_SIMPLE_MCP_WRAPPER_PATH", value, 100) ||
        wcscmp(value, L"C:\\spoof.cmd") != 0) return 6;

    SetEnvironmentVariableW(L"_SIMPLE_MCP_TEST_NEGATIVE", L"1");
    pid = rt_process_spawn_inherit();
    int64_t negative = pid <= 0 ? -1 : rt_process_wait(pid, 0);
    if (negative != -42) {
        fprintf(stderr, "negative child status=%lld\n", (long long)negative);
        return 7;
    }
    SetEnvironmentVariableW(L"_SIMPLE_MCP_TEST_NEGATIVE", NULL);

    wchar_t wrapper[32768], hidden[32768];
    if (!fixture_path(wrapper, sizeof(wrapper) / sizeof(wrapper[0]))) return 8;
    if (swprintf(hidden, sizeof(hidden) / sizeof(hidden[0]), L"%ls.hidden", wrapper) < 0)
        return 9;
    if (!MoveFileW(wrapper, hidden)) return 10;
    int64_t missing = rt_process_spawn_inherit();
    BOOL restored = MoveFileW(hidden, wrapper);
    if (!restored || missing != -1) return 11;
    CloseHandle(sentinel);
    puts("spawn-inherit PASS");
    return 0;
}
