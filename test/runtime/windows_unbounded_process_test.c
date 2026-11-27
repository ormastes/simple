/* Real Windows process owners, both RuntimeValue-array and native tuple ABIs.
 * The child uses wide argv so Unicode checks do not depend on the host ACP. */
#include "runtime.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <wchar.h>
#include <windows.h>

int64_t* rt_process_run_tuple(const char*, uint64_t, SplArray*);
int64_t* rt_process_run_timeout_tuple(const char*, uint64_t, SplArray*, int64_t);
int64_t* rt_process_run_bounded_tuple(const char*, uint64_t, SplArray*, int64_t, int64_t);
int64_t* rt_process_run_bounded_bytes_tuple(const char*, uint64_t, SplArray*, int64_t, int64_t);
enum { LARGE_OUT = 4 * 1024 * 1024 + 123, LARGE_ERR = 4 * 1024 * 1024 + 17 };

static int child(int argc, wchar_t **argv) {
    if (wcscmp(argv[1], L"inheritance") == 0) {
        wchar_t value[128];
        if (!GetEnvironmentVariableW(L"SIMPLE_UNBOUNDED_ENV_\u65e5", value, 128) ||
            wcscmp(value, L"\u65e5\u672c\u8a9e value")) return 94;
        SetLastError(ERROR_SUCCESS);
        if (GetEnvironmentVariableW(L"_SIMPLE_STACK_SET", value, 128) != 0 ||
            GetLastError() != ERROR_ENVVAR_NOT_FOUND) return 95;
        if (!GetEnvironmentVariableW(L"SIMPLE_UNBOUNDED_HANDLE", value, 128)) return 96;
        HANDLE sentinel = (HANDLE)(uintptr_t)wcstoull(value, NULL, 16);
        DWORD flags;
        SetLastError(ERROR_SUCCESS);
        if (GetHandleInformation(sentinel, &flags) || GetLastError() != ERROR_INVALID_HANDLE) return 97;
    }
    if (wcscmp(argv[1], L"args") == 0 &&
        (argc != 7 || wcscmp(argv[2], L"") || wcscmp(argv[3], L"space value") ||
         wcscmp(argv[4], L"quote\"value") || wcscmp(argv[5], L"\u65e5\u672c\u8a9e") ||
         wcscmp(argv[6], L"space trailing\\"))) return 91;
    if (wcscmp(argv[1], L"large") == 0) {
        char buffer[8192];
        memset(buffer, 'o', sizeof(buffer));
        for (size_t at = 0; at < LARGE_OUT;) {
            size_t n = LARGE_OUT - at < sizeof(buffer) ? LARGE_OUT - at : sizeof(buffer);
            if (fwrite(buffer, 1, n, stdout) != n) return 92;
            at += n;
        }
        memset(buffer, 'e', sizeof(buffer));
        for (size_t at = 0; at < LARGE_ERR;) {
            size_t n = LARGE_ERR - at < sizeof(buffer) ? LARGE_ERR - at : sizeof(buffer);
            if (fwrite(buffer, 1, n, stderr) != n) return 93;
            at += n;
        }
    } else {
        fputs("stdout-payload", stdout);
        fputs("stderr-payload", stderr);
    }
    return wcscmp(argv[1], L"exit300") == 0 ? 300 : 7;
}

static int check_text(int64_t value, const char *text, size_t length, int repeated, int bytes) {
    if (bytes) {
        SplArray *array = (SplArray*)(uintptr_t)value;
        if (rt_array_len(array) != (int64_t)length) return 0;
        for (size_t i = 0; i < length; ++i)
            if (rt_value_as_int(rt_array_get(array, i)) != (unsigned char)text[repeated ? 0 : i]) return 0;
        return 1;
    }
    if (rt_string_len(value) != (int64_t)length) return 0;
    const uint8_t *data = rt_string_data(value);
    if (!data) return 0;
    if (!repeated) return memcmp(data, text, length) == 0;
    for (size_t i = 0; i < length; ++i) if (data[i] != (uint8_t)text[0]) return 0;
    return 1;
}

static int run_case(const char *exe, const char *mode, int lane) {
    const char *selected = getenv("SIMPLE_PROCESS_PROBE_CASE");
    if (selected && strcmp(selected, mode) != 0) return 0;
    const char *names[] = {"array", "tuple", "timeout", "bounded", "bytes"};
    const char *arg_texts[] = {mode, "", "space value", "quote\"value",
        "\xe6\x97\xa5\xe6\x9c\xac\xe8\xaa\x9e", "space trailing\\"};
    int count = strcmp(mode, "args") == 0 ? 6 : 1;
    int64_t arg_values[6];
    SplArray *args = rt_array_new(count);
    for (int i = 0; i < count; ++i) {
        arg_values[i] = rt_string_new((const uint8_t*)arg_texts[i], strlen(arg_texts[i]));
        rt_array_push(args, arg_values[i]);
    }
    int64_t out, err, code;
    if (lane) {
        int64_t *t = lane == 1 ? rt_process_run_tuple(exe, strlen(exe), args) :
            lane == 2 ? rt_process_run_timeout_tuple(exe, strlen(exe), args, 30000) :
            lane == 3 ? rt_process_run_bounded_tuple(exe, strlen(exe), args, 30000, -1) :
            rt_process_run_bounded_bytes_tuple(exe, strlen(exe), args, 30000, 8 * 1024 * 1024);
        if (!t) { fprintf(stderr, "FAIL: null tuple\n"); return 1; }
        out = t[0]; err = t[1]; code = t[2];
        rt_free((uint8_t*)t);
    } else {
        SplArray *result = (SplArray*)(uintptr_t)rt_process_run(exe, strlen(exe), args);
        if (rt_array_len(result) != 3) { fprintf(stderr, "FAIL: result array shape\n"); return 1; }
        out = rt_array_get(result, 0); err = rt_array_get(result, 1);
        code = rt_value_as_int(rt_array_get(result, 2));
        rt_array_free(result);
    }
    for (int i = 0; i < count; ++i) rt_string_free(arg_values[i]);
    rt_array_free(args);
    for (int i = 0; i < 32; ++i) {
        SplArray *churn = rt_array_new(3);
        rt_array_push(churn, rt_value_int(i));
        rt_array_free(churn);
    }
    int missing = strcmp(mode, "missing") == 0;
    int large = strcmp(mode, "large") == 0;
    int bytes = lane == 4;
    int64_t out_len = bytes ? rt_array_len((SplArray*)(uintptr_t)out) : rt_string_len(out);
    int64_t err_len = bytes ? rt_array_len((SplArray*)(uintptr_t)err) : rt_string_len(err);
    int64_t expected = missing ? -1 : strcmp(mode, "exit300") == 0 ? 300 : 7;
    int good = code == expected;
    if (missing) good = good && out_len == 0 && (bytes ? err_len == 0 : err_len > 0);
    else good = good && check_text(out, large ? "o" : "stdout-payload", large ? LARGE_OUT : 14, large, bytes)
        && check_text(err, large ? "e" : "stderr-payload", large ? LARGE_ERR : 14, large, bytes);
    printf("%s abi=%s case=%s status=%lld stdout=%lld stderr=%lld\n",
        good ? "PASS" : "FAIL", names[lane], mode,
        (long long)code, (long long)out_len, (long long)err_len);
    if (bytes) { rt_array_free((SplArray*)(uintptr_t)out); rt_array_free((SplArray*)(uintptr_t)err); }
    else { rt_string_free(out); rt_string_free(err); }
    return !good;
}

int wmain(int argc, wchar_t **argv) {
    if (argc > 1) return child(argc, argv);
    wchar_t original[32768], copied[32768];
    DWORD n = GetModuleFileNameW(NULL, original, 32768);
    if (!n || n >= 32768) return 2;
    wcscpy(copied, original);
    wchar_t *base = wcsrchr(copied, L'\\');
    if (!base || (base - copied) + 64 >= 32768) return 2;
    wcscpy(base + 1, L"capture space \u65e5.exe");
    if (!CopyFileW(original, copied, TRUE)) return 2;
    char exe[131072], missing[131100];
    if (!WideCharToMultiByte(CP_UTF8, 0, copied, -1, exe, sizeof(exe), NULL, NULL)) {
        DeleteFileW(copied); return 2;
    }
    snprintf(missing, sizeof(missing), "%s.missing.exe", exe);
    const wchar_t *keys[] = {L"SIMPLE_UNBOUNDED_ENV_\u65e5", L"_SIMPLE_STACK_SET", L"SIMPLE_UNBOUNDED_HANDLE"};
    wchar_t *saved[3] = {NULL, NULL, NULL};
    for (int i = 0; i < 3; ++i) {
        DWORD needed = GetEnvironmentVariableW(keys[i], NULL, 0);
        if (needed) {
            saved[i] = (wchar_t*)calloc(needed, sizeof(wchar_t));
            if (!saved[i] || !GetEnvironmentVariableW(keys[i], saved[i], needed)) return 2;
        }
    }
    SECURITY_ATTRIBUTES security = {sizeof(security), NULL, TRUE};
    HANDLE sentinel = CreateEventW(&security, TRUE, FALSE, NULL);
    if (!sentinel) return 2;
    wchar_t handle_text[64];
    swprintf(handle_text, 64, L"%llx", (unsigned long long)(uintptr_t)sentinel);
    if (!SetEnvironmentVariableW(keys[0], L"\u65e5\u672c\u8a9e value") ||
        !SetEnvironmentVariableW(keys[1], L"probe-only") ||
        !SetEnvironmentVariableW(keys[2], handle_text)) return 2;
    int failures = 0;
    for (int tuple = 0; tuple < 5; ++tuple) {
        failures += run_case(exe, "exit7", tuple);
        failures += run_case(exe, "exit300", tuple);
        failures += run_case(exe, "args", tuple);
        failures += run_case(exe, "large", tuple);
        failures += run_case(missing, "missing", tuple);
        failures += run_case(exe, "inheritance", tuple);
    }
    CloseHandle(sentinel);
    for (int i = 0; i < 3; ++i) {
        if (!SetEnvironmentVariableW(keys[i], saved[i])) failures++;
        free(saved[i]);
    }
    if (!DeleteFileW(copied)) return 2;
    return failures ? 1 : 0;
}
