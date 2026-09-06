/*
 * Terminal primitives for the core-C bootstrap runtime.
 *
 * The public ABI is declared by std.nogc_sync_mut.tui.terminal.  Tuple
 * results are runtime tuple handles, not C aggregate returns: this is the
 * normal native ABI for an extern `-> (i64, i64)`.
 */
#include "runtime.h"

#include <stdint.h>
#include <stdbool.h>

#if defined(_WIN32)
#include <windows.h>
#include <io.h>
#else
#include <errno.h>
#include <sys/ioctl.h>
#include <termios.h>
#include <unistd.h>
#endif

static int64_t rt_terminal_size_tuple(int64_t cols, int64_t rows) {
    int64_t tuple = rt_tuple_new(2);
    if (!tuple) return 0;
    if (!rt_tuple_set(tuple, 0, rt_value_int(cols))) return 0;
    if (!rt_tuple_set(tuple, 1, rt_value_int(rows))) return 0;
    return tuple;
}

#if defined(_WIN32)
static HANDLE rt_terminal_input = INVALID_HANDLE_VALUE;
static DWORD rt_terminal_saved_mode = 0;
static int rt_terminal_raw_active = 0;

bool rt_terminal_is_tty(void) {
    DWORD mode = 0;
    HANDLE input = GetStdHandle(STD_INPUT_HANDLE);
    return input != INVALID_HANDLE_VALUE && input != NULL && GetConsoleMode(input, &mode) != 0;
}

bool rt_terminal_stdout_is_tty(void) {
    DWORD mode = 0;
    HANDLE output = GetStdHandle(STD_OUTPUT_HANDLE);
    return output != INVALID_HANDLE_VALUE && output != NULL && GetConsoleMode(output, &mode) != 0;
}

bool rt_terminal_enable_raw_mode(void) {
    DWORD mode = 0;
    HANDLE input = GetStdHandle(STD_INPUT_HANDLE);
    if (rt_terminal_raw_active) return true;
    if (input == INVALID_HANDLE_VALUE || input == NULL || !GetConsoleMode(input, &mode)) return false;
    DWORD raw = mode & ~(ENABLE_ECHO_INPUT | ENABLE_LINE_INPUT | ENABLE_PROCESSED_INPUT);
    if (!SetConsoleMode(input, raw)) return false;
    rt_terminal_input = input;
    rt_terminal_saved_mode = mode;
    rt_terminal_raw_active = 1;
    return true;
}

bool rt_terminal_disable_raw_mode(void) {
    if (!rt_terminal_raw_active) return true;
    if (rt_terminal_input == INVALID_HANDLE_VALUE || !SetConsoleMode(rt_terminal_input, rt_terminal_saved_mode)) return false;
    rt_terminal_raw_active = 0;
    rt_terminal_input = INVALID_HANDLE_VALUE;
    return true;
}

int64_t rt_terminal_get_size(void) {
    CONSOLE_SCREEN_BUFFER_INFO info;
    HANDLE output = GetStdHandle(STD_OUTPUT_HANDLE);
    if (output != INVALID_HANDLE_VALUE && output != NULL && GetConsoleScreenBufferInfo(output, &info)) {
        int64_t cols = (int64_t)(info.srWindow.Right - info.srWindow.Left + 1);
        int64_t rows = (int64_t)(info.srWindow.Bottom - info.srWindow.Top + 1);
        if (cols > 0 && rows > 0) return rt_terminal_size_tuple(cols, rows);
    }
    return rt_terminal_size_tuple(80, 24);
}

int64_t rt_stdin_read_byte(void) {
    unsigned char byte = 0;
    DWORD read_count = 0;
    HANDLE input = GetStdHandle(STD_INPUT_HANDLE);
    if (input == INVALID_HANDLE_VALUE || input == NULL) return -1;
    return ReadFile(input, &byte, 1, &read_count, NULL) && read_count == 1 ? (int64_t)byte : -1;
}
#else
static struct termios rt_terminal_saved_mode;
static int rt_terminal_raw_active = 0;

bool rt_terminal_is_tty(void) {
    return isatty(STDIN_FILENO) == 1;
}

bool rt_terminal_stdout_is_tty(void) {
    return isatty(STDOUT_FILENO) == 1;
}

bool rt_terminal_enable_raw_mode(void) {
    struct termios raw;
    if (rt_terminal_raw_active) return true;
    if (!rt_terminal_is_tty() || tcgetattr(STDIN_FILENO, &rt_terminal_saved_mode) != 0) return false;
    raw = rt_terminal_saved_mode;
    raw.c_iflag &= (tcflag_t)~(IGNBRK | BRKINT | PARMRK | ISTRIP | INLCR | IGNCR | ICRNL | IXON);
    raw.c_oflag &= (tcflag_t)~OPOST;
    raw.c_lflag &= (tcflag_t)~(ECHO | ECHONL | ICANON | ISIG | IEXTEN);
    raw.c_cflag &= (tcflag_t)~(CSIZE | PARENB);
    raw.c_cflag |= CS8;
    raw.c_cc[VMIN] = 1;
    raw.c_cc[VTIME] = 0;
    if (tcsetattr(STDIN_FILENO, TCSAFLUSH, &raw) != 0) return false;
    rt_terminal_raw_active = 1;
    return true;
}

bool rt_terminal_disable_raw_mode(void) {
    if (!rt_terminal_raw_active) return true;
    if (tcsetattr(STDIN_FILENO, TCSAFLUSH, &rt_terminal_saved_mode) != 0) return false;
    rt_terminal_raw_active = 0;
    return true;
}

int64_t rt_terminal_get_size(void) {
    struct winsize size;
    if (ioctl(STDOUT_FILENO, TIOCGWINSZ, &size) == 0 && size.ws_col > 0 && size.ws_row > 0) {
        return rt_terminal_size_tuple((int64_t)size.ws_col, (int64_t)size.ws_row);
    }
    return rt_terminal_size_tuple(80, 24);
}

int64_t rt_stdin_read_byte(void) {
    unsigned char byte = 0;
    ssize_t read_count;
    do {
        read_count = read(STDIN_FILENO, &byte, 1);
    } while (read_count < 0 && errno == EINTR);
    return read_count == 1 ? (int64_t)byte : -1;
}
#endif
