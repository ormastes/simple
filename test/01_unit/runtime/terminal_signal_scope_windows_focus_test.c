#include "runtime.h"

#include <assert.h>
#include <stdio.h>

#if defined(_WIN32)
#include <windows.h>
#include "runtime_terminal_signal_scope_impl.h"
#include "runtime_terminal_mode_impl.h"

int main(void) {
    HANDLE input = GetStdHandle(STD_INPUT_HANDLE);
    DWORD before = 0;
    if (input == NULL || input == INVALID_HANDLE_VALUE || !GetConsoleMode(input, &before)) {
        fputs("terminal-signal-scope-windows: BLOCKED (real console unavailable)\n", stderr);
        return 77;
    }

    int64_t scope = rt_terminal_signal_scope_begin();
    assert(scope > 0);
    assert(rt_terminal_enable_raw_mode());
    DWORD raw = 0;
    assert(GetConsoleMode(input, &raw));
    assert((raw & (ENABLE_ECHO_INPUT | ENABLE_LINE_INPUT | ENABLE_PROCESSED_INPUT)) == 0);
    assert((raw & ENABLE_WINDOW_INPUT) != 0);

    INPUT_RECORD resize = {0};
    resize.EventType = WINDOW_BUFFER_SIZE_EVENT;
    resize.Event.WindowBufferSizeEvent.dwSize.X = 100;
    resize.Event.WindowBufferSizeEvent.dwSize.Y = 40;
    DWORD written = 0;
    assert(WriteConsoleInputW(input, &resize, 1, &written));
    assert(written == 1);
    assert(rt_terminal_read_byte_interruptible(scope) == -3);

    assert(rt_terminal_disable_raw_mode());
    assert(rt_terminal_signal_scope_end(scope));
    DWORD after = 0;
    assert(GetConsoleMode(input, &after));
    assert(after == before);
    return 0;
}

#else

int main(void) {
    fputs("terminal-signal-scope-windows: BLOCKED (requires Windows)\n", stderr);
    return 77;
}

#endif
