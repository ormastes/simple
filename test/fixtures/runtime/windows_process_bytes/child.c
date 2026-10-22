#include <windows.h>
#include <stdio.h>
#include <wchar.h>
#include <io.h>
#include <fcntl.h>

int wmain(int argc, wchar_t** argv) {
    _setmode(_fileno(stdout), _O_BINARY);
    _setmode(_fileno(stderr), _O_BINARY);
    if (argc < 2) return 90;
    if (!wcscmp(argv[1], L"echo") && argc == 3) {
        char bytes[4096];
        int count = WideCharToMultiByte(CP_UTF8, WC_ERR_INVALID_CHARS, argv[2], -1, bytes, sizeof(bytes), NULL, NULL);
        if (!count) return 91;
        fwrite(bytes, 1, count - 1, stdout);
        fwrite(bytes, 1, count - 1, stderr);
        return 7;
    }
    if (!wcscmp(argv[1], L"malformed")) {
        const unsigned char raw[] = {'A', 0, 255, 0xe2, 0x82};
        fwrite(raw, 1, sizeof(raw), stdout);
        fwrite(raw, 1, sizeof(raw), stderr);
        return 9;
    }
    if (!wcscmp(argv[1], L"cap")) {
        for (int i = 0; i < 32768; ++i) { fputc('A' + i % 26, stdout); fputc('a' + i % 26, stderr); }
        return 0;
    }
    if (!wcscmp(argv[1], L"sleep")) { Sleep(10000); return 0; }
    if (!wcscmp(argv[1], L"tree") || !wcscmp(argv[1], L"root-exit")) {
        wchar_t line[8192];
        if (swprintf(line, 8192, L"\"%ls\" sleep", argv[0]) < 0) return 92;
        STARTUPINFOW startup = {sizeof(startup)};
        PROCESS_INFORMATION process = {0};
        if (!CreateProcessW(argv[0], line, NULL, NULL, TRUE, 0, NULL, NULL, &startup, &process)) return 93;
        CloseHandle(process.hThread);
        CloseHandle(process.hProcess);
        fprintf(stdout, "%lu", process.dwProcessId);
        fflush(stdout);
        if (!wcscmp(argv[1], L"tree")) Sleep(10000);
        return 0;
    }
    return 94;
}
