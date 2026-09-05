#ifndef SIMPLE_RUNTIME_TERMINAL_MODE_IMPL_H
#define SIMPLE_RUNTIME_TERMINAL_MODE_IMPL_H

#include <stdbool.h>

#ifndef SPL_TERMINAL_ENABLE_RAW_MODE
#define SPL_TERMINAL_ENABLE_RAW_MODE rt_terminal_enable_raw_mode
#endif
#ifndef SPL_TERMINAL_DISABLE_RAW_MODE
#define SPL_TERMINAL_DISABLE_RAW_MODE rt_terminal_disable_raw_mode
#endif

#if defined(_WIN32)
#include <io.h>
#include <windows.h>
static DWORD spl_terminal_saved_console_mode;
static bool spl_terminal_has_saved_console_mode;

bool SPL_TERMINAL_ENABLE_RAW_MODE(void) {
    HANDLE input = GetStdHandle(STD_INPUT_HANDLE);
    DWORD mode = 0;
    if (spl_terminal_has_saved_console_mode || input == INVALID_HANDLE_VALUE ||
        !GetConsoleMode(input, &mode)) return false;
    DWORD raw = mode & ~(ENABLE_ECHO_INPUT | ENABLE_LINE_INPUT | ENABLE_PROCESSED_INPUT);
    raw |= ENABLE_WINDOW_INPUT;
    if (!SetConsoleMode(input, raw)) return false;
    spl_terminal_saved_console_mode = mode;
    spl_terminal_has_saved_console_mode = true;
    return true;
}

bool SPL_TERMINAL_DISABLE_RAW_MODE(void) {
    if (!spl_terminal_has_saved_console_mode) return true;
    HANDLE input = GetStdHandle(STD_INPUT_HANDLE);
    if (input == INVALID_HANDLE_VALUE ||
        !SetConsoleMode(input, spl_terminal_saved_console_mode)) return false;
    spl_terminal_has_saved_console_mode = false;
    return true;
}
#else
#include <termios.h>
#include <unistd.h>
static struct termios spl_terminal_saved_termios;
static bool spl_terminal_has_saved_termios;

bool SPL_TERMINAL_ENABLE_RAW_MODE(void) {
    struct termios raw;
    if (spl_terminal_has_saved_termios ||
        tcgetattr(STDIN_FILENO, &spl_terminal_saved_termios) != 0) return false;
    raw = spl_terminal_saved_termios;
    cfmakeraw(&raw);
    if (tcsetattr(STDIN_FILENO, TCSANOW, &raw) != 0) return false;
    spl_terminal_has_saved_termios = true;
    return true;
}

bool SPL_TERMINAL_DISABLE_RAW_MODE(void) {
    if (!spl_terminal_has_saved_termios) return true;
    if (tcsetattr(STDIN_FILENO, TCSANOW, &spl_terminal_saved_termios) != 0) return false;
    spl_terminal_has_saved_termios = false;
    return true;
}
#endif

#undef SPL_TERMINAL_ENABLE_RAW_MODE
#undef SPL_TERMINAL_DISABLE_RAW_MODE

#endif
