/* T1 reference fixture — termbox2.
 *
 * Reference-only. Not a production backend. Implements the T1 terminal
 * contract from doc/01_research/ui/slim_kernel_plugin/
 * simple_slim_tui_gui_kernel_plugin_design_parallel_plan_2026-09-05.md 8.1:
 *   80x24, clear screen, bordered panel with the greeting, a status line,
 *   wait for a single key ('q' quits), restore the terminal.
 *
 * Exit codes (contract shared with the ncursesw fixture):
 *   0  clean T1 run, terminal restored
 *   2  refusing to run: stdin or stdout is not a tty (NOT a T1 run)
 *   3  terminal is not exactly 80x24
 *   4  initialization failed
 *   5  input error / EOF before a key arrived
 */
#define TB_IMPL
#include "../vendor/termbox2/termbox2.h"

#include <stdio.h>
#include <unistd.h>

#define T1_COLS 80
#define T1_ROWS 24
#define T1_GREETING "Hello from Simple UI!"
#define T1_STATUS "status: ready | press q to quit"

static void draw_panel(int x, int y, int w, int h) {
    int i;
    for (i = 1; i < w - 1; i++) {
        tb_set_cell(x + i, y, 0x2500, TB_WHITE, TB_DEFAULT);
        tb_set_cell(x + i, y + h - 1, 0x2500, TB_WHITE, TB_DEFAULT);
    }
    for (i = 1; i < h - 1; i++) {
        tb_set_cell(x, y + i, 0x2502, TB_WHITE, TB_DEFAULT);
        tb_set_cell(x + w - 1, y + i, 0x2502, TB_WHITE, TB_DEFAULT);
    }
    tb_set_cell(x, y, 0x250C, TB_WHITE, TB_DEFAULT);
    tb_set_cell(x + w - 1, y, 0x2510, TB_WHITE, TB_DEFAULT);
    tb_set_cell(x, y + h - 1, 0x2514, TB_WHITE, TB_DEFAULT);
    tb_set_cell(x + w - 1, y + h - 1, 0x2518, TB_WHITE, TB_DEFAULT);
}

int main(void) {
    struct tb_event ev;
    int rv;

    /* termbox2's tb_init() falls back to opening /dev/tty, so it would happily
     * initialize with stdout redirected to a file. That would silently turn a
     * non-interactive run into something that looks like T1. Refuse first. */
    if (!isatty(STDIN_FILENO) || !isatty(STDOUT_FILENO)) {
        fprintf(stderr, "t1_termbox2: refusing to run: stdin/stdout is not a tty\n");
        return 2;
    }

    rv = tb_init_rwfd(STDIN_FILENO, STDOUT_FILENO);
    if (rv != TB_OK) {
        fprintf(stderr, "t1_termbox2: tb_init_rwfd failed: %s\n", tb_strerror(rv));
        return 4;
    }

    if (tb_width() != T1_COLS || tb_height() != T1_ROWS) {
        int w = tb_width(), h = tb_height();
        tb_shutdown();
        fprintf(stderr, "t1_termbox2: terminal is %dx%d, T1 requires %dx%d\n",
                w, h, T1_COLS, T1_ROWS);
        return 3;
    }

    tb_clear();
    draw_panel(2, 2, T1_COLS - 4, T1_ROWS - 6);
    tb_print(4, 4, TB_WHITE | TB_BOLD, TB_DEFAULT, T1_GREETING);
    tb_print(2, T1_ROWS - 2, TB_WHITE, TB_DEFAULT, T1_STATUS);
    tb_present();

    for (;;) {
        rv = tb_poll_event(&ev);
        if (rv != TB_OK) {
            tb_shutdown();
            fprintf(stderr, "t1_termbox2: tb_poll_event failed: %s\n", tb_strerror(rv));
            return 5;
        }
        if (ev.type == TB_EVENT_KEY && ev.ch == 'q') break;
        if (ev.type == TB_EVENT_RESIZE) {
            tb_present(); /* T1 freezes the size; repaint is a no-op redraw */
        }
    }

    tb_shutdown();
    return 0;
}
