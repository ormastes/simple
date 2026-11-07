/* SOURCE-ONLY test peer. Not GDB admission evidence. Never touches hardware.
 * Compile separately after source review/resource authorization.
 * normal: consume frames promptly; partial: consume 17 bytes every 20 ms;
 * nonreader: leave stdin open without ever issuing ReadFile.
 * stdout prefix gives the controller an actual ready handshake.
 */
#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <stdio.h>
#include <string.h>
#include <stdint.h>

int main(int argc, char **argv) {
    HANDLE input = GetStdHandle(STD_INPUT_HANDLE);
    HANDLE output = GetStdHandle(STD_OUTPUT_HANDLE);
    if (argc != 2 || input == INVALID_HANDLE_VALUE || output == INVALID_HANDLE_VALUE) return 64;
    int partial = strcmp(argv[1], "partial") == 0;
    int nonreader = strcmp(argv[1], "nonreader") == 0;
    if (!partial && !nonreader && strcmp(argv[1], "normal") != 0) return 65;
    DWORD written = 0;
    const char ready[] = "=peer-ready\n";
    if (!WriteFile(output, ready, sizeof(ready) - 1, &written, NULL) || written != sizeof(ready) - 1) return 66;
    if (nonreader) {
        /* Finite safety backstop, deliberately exceeds the 6 second MI budget.
         * Controller must prove pending/zero write and retire us before 30 s.
         */
        Sleep(30000);
        return 67;
    }
    char chunk[4096];
    char token[16];
    size_t token_len = 0;
    uint64_t bytes = 0, hash = UINT64_C(14695981039346656037);
    int token_done = 0;
    for (;;) {
        DWORD count = 0;
        if (!ReadFile(input, chunk, partial ? 17 : sizeof(chunk), &count, NULL)) return GetLastError() == ERROR_BROKEN_PIPE ? 0 : 68;
        if (!count) return 0;
        for (DWORD i = 0; i < count; ++i) {
            unsigned char byte = (unsigned char)chunk[i];
            if (byte == '\n') {
                char reply[160];
                token[token_len] = 0;
                if (!token_len) return 69;
                int n = snprintf(reply, sizeof(reply), "%s^done,bytes=\"%llu\",fnv1a64=\"%016llx\"\n", token, (unsigned long long)bytes, (unsigned long long)hash);
                if (n <= 0 || n >= (int)sizeof(reply)) return 70;
                if (!WriteFile(output, reply, (DWORD)n, &written, NULL) || written != (DWORD)n) return 71;
                token_len = 0; token_done = 0; bytes = 0;
                hash = UINT64_C(14695981039346656037);
            } else {
                if (!token_done && byte >= '0' && byte <= '9') {
                    if (token_len >= sizeof(token) - 1) return 72;
                    token[token_len++] = (char)byte;
                } else token_done = 1;
                ++bytes; hash = (hash ^ byte) * UINT64_C(1099511628211);
            }
        }
        if (partial) Sleep(20);
    }
}
