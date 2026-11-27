/* Windows console UTF-8 write path (runtime_console_utf8_private.h).
 * Allocates a private console, forces output code page 437 (where raw UTF-8
 * bytes garble), writes UTF-8 through rt_console_write_utf8 -- including a
 * scalar split across two writes -- and reads the screen back as UTF-16.
 * Also checks that a pipe is NOT treated as a console (raw bytes kept).
 * Build: clang-cl /nologo src/runtime/test/rt_console_utf8_selfcheck.c */
#ifdef _WIN32
#include "../runtime_console_utf8_private.h"
#include <fcntl.h>

static int failures = 0;
static FILE* g_log;

static void check(const char* what, int ok) {
    fprintf(g_log, "%s %s\n", ok ? "ok  " : "FAIL", what);
    if (!ok) failures++;
}

static int screen_has(HANDLE out, const wchar_t* want, int row) {
    wchar_t line[64] = {0};
    DWORD n = 0;
    COORD at = {0, (SHORT)row};
    ReadConsoleOutputCharacterW(out, line, 63, at, &n);
    return wcsncmp(line, want, wcslen(want)) == 0;
}

int main(void) {
    g_log = fopen("rt_console_utf8_selfcheck.log", "w");
    setvbuf(g_log, NULL, _IONBF, 0);
    FreeConsole();
    if (!AllocConsole()) { fprintf(g_log, "SKIP - no console available\n"); return 77; }
    SetConsoleOutputCP(437);
    HANDLE out = CreateFileA("CONOUT$", GENERIC_READ | GENERIC_WRITE, FILE_SHARE_READ | FILE_SHARE_WRITE, NULL, OPEN_EXISTING, 0, NULL);
    SetStdHandle(STD_OUTPUT_HANDLE, out);
    _dup2(_open_osfhandle((intptr_t)out, _O_BINARY), 1); /* read+write handle: GetConsoleMode needs GENERIC_READ */

    /* e-acute (C3 A9) + CJK (E7 95 8C), whole */
    check("console detected", rt_console_write_utf8(stdout, (const uint8_t*)"\xC3\xA9\xE7\x95\x8C\n", 6));
    check("whole scalars decoded", screen_has(out, L"é界", 0));
    /* split: E7 95 | 8C (3-byte scalar across two writes) */
    rt_console_write_utf8(stdout, (const uint8_t*)"\xE7\x95", 2);
    rt_console_write_utf8(stdout, (const uint8_t*)"\x8C\n", 2);
    check("split scalar joined", screen_has(out, L"界", 1));
    /* malformed byte -> U+FFFD */
    rt_console_write_utf8(stdout, (const uint8_t*)"a\xFF" "b\n", 4);
    check("malformed -> U+FFFD", screen_has(out, L"a\xFFFD" L"b", 2));

    /* 4-byte scalar cuts (conhost read-back shows non-BMP as U+FFFD, so pin the splitter directly) */
    {
        const uint8_t e[] = {0x61, 0xF0, 0x9F, 0x98, 0x80};
        check("4-byte cut after 1 held", rt_con_complete_prefix(e, 2) == 1);
        check("4-byte cut after 3 held", rt_con_complete_prefix(e, 4) == 1);
        check("4-byte whole kept", rt_con_complete_prefix(e, 5) == 5);
    }

    /* A pipe handle is not a console: raw path. */
    HANDLE rd, wr;
    CreatePipe(&rd, &wr, NULL, 0);
    int pfd = _open_osfhandle((intptr_t)wr, 0);
    _dup2(pfd, 2); /* stderr now a pipe */
    check("pipe is not a console", rt_console_write_utf8(stderr, (const uint8_t*)"x", 1) == 0);

    FreeConsole();
    if (failures) { fprintf(g_log, "FAIL - %d check(s) failed\n", failures); return 1; }
    fprintf(g_log, "PASS - windows console utf-8 write path\n");
    return 0;
}
#else
int main(void) { return 0; } /* Windows console path only. */
#endif
