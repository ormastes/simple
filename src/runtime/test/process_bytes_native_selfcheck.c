/* Real runtime boundary witness, used in both C-only and mixed native links. */
#include "runtime.h"
#include <windows.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int checks, failures;
#define CHECK(condition) do { ++checks; if (!(condition)) { ++failures; fprintf(stderr, "FAIL process bytes line %d\n", __LINE__); } } while (0)
static int64_t capture(const char* exe, const char* mode, const char* value, int64_t timeout, int64_t cap) {
    SplArray* args = rt_array_new(2);
    rt_array_push(args, rt_string_new((const uint8_t*)mode, strlen(mode)));
    if (value) rt_array_push(args, rt_string_new((const uint8_t*)value, strlen(value)));
    int64_t result = rt_process_run_bounded_bytes(exe, strlen(exe), args, timeout, cap);
    rt_array_free(args);
    return result;
}
static int bytes_equal(int64_t array, const unsigned char* bytes, size_t size) {
    if ((uint64_t)rt_array_len((SplArray*)(uintptr_t)array) != size) return 0;
    for (size_t i = 0; i < size; ++i)
        if (rt_value_as_int(rt_array_get((SplArray*)(uintptr_t)array, i)) != bytes[i]) return 0;
    return 1;
}
static int64_t code(int64_t result) { return rt_value_as_int(rt_tuple_get(result, 2)); }

static int fixture_executable(char* exe, int capacity) {
    wchar_t wide[16384];
    DWORD len = GetEnvironmentVariableW(L"SIMPLE_PROCESS_BYTES_CHILD", wide, 16384);
    return len && len < 16384 && WideCharToMultiByte(CP_UTF8, WC_ERR_INVALID_CHARS, wide, -1, exe, capacity, NULL, NULL);
}

int64_t process_bytes_malformed_fixture(void) {
    char exe[65536];
    if (!fixture_executable(exe, sizeof(exe))) return 0;
    return capture(exe, "malformed", NULL, 3000, 4096);
}

int64_t process_bytes_unicode_fixture(void) {
    char exe[65536];
    if (!fixture_executable(exe, sizeof(exe))) return 0;
    return capture(exe, "echo", "\xed\x95\x9c\xea\xb8\x80 \xf0\x9f\x98\x80", 3000, 4096);
}

int64_t process_bytes_prelaunch_selfcheck(void) {
    int failed = 0;
    const char* missing = "Z:/__simple_missing_process_bytes__/absent.exe";
    int64_t result = capture(missing, "echo", NULL, 1000, 1024);
    if (code(result) != -1 || !bytes_equal(rt_tuple_get(result, 0), NULL, 0) ||
        !bytes_equal(rt_tuple_get(result, 1), NULL, 0)) ++failed;
    result = rt_process_run_bounded_bytes("", 0, NULL, 1000, 16);
    if (code(result) != -1 || !bytes_equal(rt_tuple_get(result, 0), NULL, 0) ||
        !bytes_equal(rt_tuple_get(result, 1), NULL, 0)) ++failed;
    printf("raw prelaunch failures retain no invented capture: %d failures\n", failed);
    return failed;
}

int64_t process_bytes_native_selfcheck(void) {
    char exe[65536];
    if (!fixture_executable(exe, sizeof(exe))) return 100;
    const char* unicode = "\xed\x95\x9c\xea\xb8\x80 \xf0\x9f\x98\x80 quoted \"argument\" \\";
    int64_t result = capture(exe, "echo", unicode, 3000, 4096);
    CHECK(code(result) == 7);
    CHECK(bytes_equal(rt_tuple_get(result, 0), (const unsigned char*)unicode, strlen(unicode)));
    CHECK(bytes_equal(rt_tuple_get(result, 1), (const unsigned char*)unicode, strlen(unicode)));
    const unsigned char malformed[] = {'A', 0, 255, 0xe2, 0x82};
    result = capture(exe, "malformed", NULL, 3000, 4096);
    CHECK(code(result) == 9);
    CHECK(bytes_equal(rt_tuple_get(result, 0), malformed, sizeof(malformed)));
    CHECK(bytes_equal(rt_tuple_get(result, 1), malformed, sizeof(malformed)));
    unsigned char out[33], err[33];
    for (int i = 0; i < 33; ++i) { out[i] = 'A' + i % 26; err[i] = 'a' + i % 26; }
    result = capture(exe, "cap", NULL, 3000, 33);
    CHECK(code(result) == 0);
    CHECK(bytes_equal(rt_tuple_get(result, 0), out, 33));
    CHECK(bytes_equal(rt_tuple_get(result, 1), err, 33));
    result = capture(exe, "cap", NULL, 3000, 0);
    CHECK(code(result) == 0);
    CHECK(bytes_equal(rt_tuple_get(result, 0), NULL, 0));
    CHECK(bytes_equal(rt_tuple_get(result, 1), NULL, 0));
    result = capture(exe, "sleep", NULL, 50, 0);
    CHECK(code(result) == -1);
    CHECK(bytes_equal(rt_tuple_get(result, 0), NULL, 0));
    CHECK(bytes_equal(rt_tuple_get(result, 1), NULL, 0));
    const char* modes[] = {"tree", "root-exit"};
    for (int mode = 0; mode < 2; ++mode) {
        ULONGLONG started = GetTickCount64();
        result = capture(exe, modes[mode], NULL, 1500, 128);
        CHECK(GetTickCount64() - started < 4000);
        CHECK(code(result) == (mode == 0 ? -1 : 0));
        int64_t bytes = rt_tuple_get(result, 0);
        int64_t count = rt_array_len((SplArray*)(uintptr_t)bytes);
        char pid_text[32] = {0};
        CHECK(count > 0 && count < 31);
        for (int64_t i = 0; i < count && i < 31; ++i) pid_text[i] = (char)rt_value_as_int(rt_array_get((SplArray*)(uintptr_t)bytes, i));
        DWORD pid = strtoul(pid_text, NULL, 10);
        CHECK(pid > 0);
        HANDLE child = OpenProcess(SYNCHRONIZE, FALSE, pid);
        CHECK(!child || WaitForSingleObject(child, 2000) == WAIT_OBJECT_0);
        if (child) CloseHandle(child);
    }
    printf("process bytes native: %d checks, %d failures\n", checks, failures);
    return failures;
}
