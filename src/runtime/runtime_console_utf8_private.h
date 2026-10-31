#ifndef SIMPLE_RUNTIME_CONSOLE_UTF8_PRIVATE_H
#define SIMPLE_RUNTIME_CONSOLE_UTF8_PRIVATE_H
/* Windows real-console output: UTF-8 -> UTF-16 -> WriteConsoleW.
 *
 * Raw bytes written to a console are decoded in the console's output code
 * page (CP437 renders UTF-8 as garbage), and SetConsoleOutputCP outlives the
 * process (ExitProcess skips atexit), so convert per write instead. Only used
 * when GetConsoleMode succeeds on the stream's handle; pipes and files keep
 * raw bytes. Malformed UTF-8 becomes U+FFFD (MultiByteToWideChar, flags 0). A
 * scalar split across two writes is held (<= 3 bytes per stream) and joined
 * with the next write; it is dropped if the process ends first. */
#if defined(_WIN32)
#include <io.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <windows.h>

static size_t rt_con_complete_prefix(const uint8_t* b, size_t n) {
    for (size_t back = 1; back <= 3 && back <= n; back++) {
        size_t i = n - back;
        uint8_t c = b[i];
        if ((c & 0xC0) == 0x80) continue;
        size_t need = (c >= 0xF0 && c <= 0xF4) ? 4 : (c >= 0xE0 && c <= 0xEF) ? 3 : (c >= 0xC2 && c <= 0xDF) ? 2 : 1;
        return need > back ? i : n;
    }
    return n;
}

/* Returns 1 when the bytes were written to a console, 0 to use the raw path. */
static int rt_console_write_utf8(FILE* stream, const uint8_t* ptr, size_t len) {
    static uint8_t tail[2][3];
    static size_t tail_n[2];
    static volatile LONG lock;
    if (stream != stdout && stream != stderr) return 0;
    int fd = _fileno(stream);
    if (fd < 0) return 0;
    HANDLE h = (HANDLE)_get_osfhandle(fd);
    DWORD mode = 0;
    if (h == INVALID_HANDLE_VALUE || !GetConsoleMode(h, &mode)) return 0;
    int slot = stream == stderr ? 1 : 0;
    while (InterlockedExchange(&lock, 1) != 0) Sleep(0);
    fflush(stream); /* keep order with stdio-buffered writers */
    size_t total = tail_n[slot] + len;
    uint8_t* buf = total ? (uint8_t*)malloc(total) : NULL;
    if (!buf) { InterlockedExchange(&lock, 0); return total == 0; }
    memcpy(buf, tail[slot], tail_n[slot]);
    if (len) memcpy(buf + tail_n[slot], ptr, len);
    size_t keep = rt_con_complete_prefix(buf, total);
    tail_n[slot] = total - keep;
    if (tail_n[slot]) memcpy(tail[slot], buf + keep, tail_n[slot]);
    int wn = keep ? MultiByteToWideChar(CP_UTF8, 0, (const char*)buf, (int)keep, NULL, 0) : 0;
    wchar_t* wbuf = wn > 0 ? (wchar_t*)malloc((size_t)wn * sizeof(wchar_t)) : NULL;
    if (wbuf && MultiByteToWideChar(CP_UTF8, 0, (const char*)buf, (int)keep, wbuf, wn) == wn) {
        int pos = 0;
        while (pos < wn) {
            int end = pos + 8192 < wn ? pos + 8192 : wn;
            if (end < wn && wbuf[end - 1] >= 0xD800 && wbuf[end - 1] < 0xDC00) end--; /* keep surrogate pair whole */
            DWORD written = 0;
            if (!WriteConsoleW(h, wbuf + pos, (DWORD)(end - pos), &written, NULL) || written == 0) break;
            pos += (int)written;
        }
    }
    free(wbuf);
    free(buf);
    InterlockedExchange(&lock, 0);
    return 1;
}
#endif
#endif
