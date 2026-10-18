/* Link with the genuine core-C runtime. No replacement runtime exports. */
#ifdef _WIN32
#include "runtime.h"
#include <windows.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

static int child(void) {
    char input[4] = {0};
    DWORD size = 0;
    if (!ReadFile(GetStdHandle(STD_INPUT_HANDLE), input, 3, &size, NULL) ||
        size != 3 || memcmp(input, "IN\n", 3)) return 91;
    if (!WriteFile(GetStdHandle(STD_OUTPUT_HANDLE), "ASYNC_OUT\n", 10, &size, NULL) || size != 10) return 92;
    if (!WriteFile(GetStdHandle(STD_ERROR_HANDLE), "ASYNC_ERR\n", 10, &size, NULL) || size != 10) return 93;
    return 23;
}

static int null_child(void) {
    DWORD size = 99;
    char byte;
    if (!ReadFile(GetStdHandle(STD_INPUT_HANDLE), &byte, 1, &size, NULL) || size != 0) return 94;
    if (!WriteFile(GetStdHandle(STD_OUTPUT_HANDLE), "x", 1, &size, NULL) || size != 1) return 95;
    if (!WriteFile(GetStdHandle(STD_ERROR_HANDLE), "y", 1, &size, NULL) || size != 1) return 96;
    return 24;
}

static int read_exact(HANDLE pipe, const char* expected) {
    char bytes[64] = {0};
    DWORD count = 0;
    return ReadFile(pipe, bytes, sizeof(bytes), &count, NULL) &&
        count == strlen(expected) && memcmp(bytes, expected, count) == 0;
}

int main(int argc, char** argv) {
    if (argc == 3 && strcmp(argv[1], "--child") == 0) {
        DWORD flags = 0;
        HANDLE unrelated = (HANDLE)(uintptr_t)_strtoui64(argv[2], NULL, 10);
        if (GetHandleInformation(unrelated, &flags)) return 97;
        return child();
    }
    if (argc == 2 && strcmp(argv[1], "--child") == 0) return child();
    if (argc == 2 && strcmp(argv[1], "--null-child") == 0) return null_child();
    if (argc == 2 && strcmp(argv[1], "--sleep-child") == 0) { Sleep(200); return 25; }
    char executable[32768];
    DWORD length = GetModuleFileNameA(NULL, executable, sizeof(executable));
    if (!length || length >= sizeof(executable)) return 1;
    HANDLE saved[3] = {GetStdHandle(STD_INPUT_HANDLE), GetStdHandle(STD_OUTPUT_HANDLE),
                       GetStdHandle(STD_ERROR_HANDLE)};
    HANDLE input_read = NULL, input_write = NULL, output_read = NULL, output_write = NULL;
    HANDLE error_read = NULL, error_write = NULL;
    /* Deliberately non-inheritable originals: the owner must duplicate them. */
    if (!CreatePipe(&input_read, &input_write, NULL, 0) ||
        !CreatePipe(&output_read, &output_write, NULL, 0) ||
        !CreatePipe(&error_read, &error_write, NULL, 0)) return 2;
    DWORD count = 0;
    if (!WriteFile(input_write, "IN\n", 3, &count, NULL) || count != 3) return 3;
    CloseHandle(input_write);
    if (!SetStdHandle(STD_INPUT_HANDLE, input_read) ||
        !SetStdHandle(STD_OUTPUT_HANDLE, output_write) ||
        !SetStdHandle(STD_ERROR_HANDLE, error_write)) return 4;
    SECURITY_ATTRIBUTES security = {sizeof(security), NULL, TRUE};
    HANDLE unrelated = CreateEventW(&security, TRUE, FALSE, NULL);
    if (!unrelated) return 10;
    char handle_text[32];
    snprintf(handle_text, sizeof(handle_text), "%llu", (unsigned long long)(uintptr_t)unrelated);
    const char* args[] = {"--child", handle_text};
    int64_t pid = rt_process_spawn_async(executable, args, 2);
    SetStdHandle(STD_INPUT_HANDLE, saved[0]);
    SetStdHandle(STD_OUTPUT_HANDLE, saved[1]);
    SetStdHandle(STD_ERROR_HANDLE, saved[2]);
    CloseHandle(input_read); CloseHandle(output_write); CloseHandle(error_write);
    CloseHandle(unrelated);
    if (pid <= 0 || rt_process_wait(pid, 5000) != 23) return 5;
    if (!read_exact(output_read, "ASYNC_OUT\n") || !read_exact(error_read, "ASYNC_ERR\n")) return 6;
    CloseHandle(output_read); CloseHandle(error_read);
    if (rt_process_wait(pid, 1) != -1) return 7; /* reaped registry entry */
    SetStdHandle(STD_INPUT_HANDLE, NULL);
    SetStdHandle(STD_OUTPUT_HANDLE, INVALID_HANDLE_VALUE);
    SetStdHandle(STD_ERROR_HANDLE, NULL);
    const char* null_args[] = {"--null-child"};
    pid = rt_process_spawn_async(executable, null_args, 1);
    SetStdHandle(STD_INPUT_HANDLE, saved[0]);
    SetStdHandle(STD_OUTPUT_HANDLE, saved[1]);
    SetStdHandle(STD_ERROR_HANDLE, saved[2]);
    if (pid <= 0 || rt_process_wait(pid, 5000) != 24 || rt_process_wait(pid, 1) != -1) return 8;
    if (rt_process_spawn_async("C:/missing/async-selfcheck.exe", NULL, 0) != -1) return 9;
    const char* sleep_args[] = {"--sleep-child"};
    pid = rt_process_spawn_async(executable, sleep_args, 1);
    if (pid <= 0 || rt_process_wait(pid, 1) != -2 || rt_process_wait(pid, 5000) != 25 ||
        rt_process_wait(pid, 1) != -1) return 11;
    puts("WINDOWS_ASYNC_STDIO_PASS");
    return 0;
}
#endif
