/* T1 reference fixture — ncursesw (wide-character ncurses).
 *
 * Reference-only. Not a production backend. Same T1 contract and the same
 * exit codes as ../termbox2/t1_termbox2.c.
 */
#include <locale.h>
#include <ncurses.h>
#include <stdio.h>
#include <unistd.h>

#define T1_COLS 80
#define T1_ROWS 24
#define T1_GREETING "Hello from Simple UI!"
#define T1_STATUS "status: ready | press q to quit"

int main(void) {
    SCREEN *scr;
    WINDOW *panel;
    int ch;

    /* newterm() would accept a redirected stdout and paint into a file. That
     * is not a terminal run, so it must never be reported as T1. */
    if (!isatty(STDIN_FILENO) || !isatty(STDOUT_FILENO)) {
        fprintf(stderr, "t1_ncursesw: refusing to run: stdin/stdout is not a tty\n");
        return 2;
    }

    setlocale(LC_ALL, "");

    scr = newterm(NULL, stdout, stdin);
    if (scr == NULL) {
        fprintf(stderr, "t1_ncursesw: newterm failed (unknown TERM or no terminfo)\n");
        return 4;
    }
    set_term(scr);

    if (COLS != T1_COLS || LINES != T1_ROWS) {
        int w = COLS, h = LINES;
        endwin();
        delscreen(scr);
        fprintf(stderr, "t1_ncursesw: terminal is %dx%d, T1 requires %dx%d\n",
                w, h, T1_COLS, T1_ROWS);
        return 3;
    }

    cbreak();
    noecho();
    keypad(stdscr, TRUE);
    curs_set(0);

    clear();
    panel = newwin(T1_ROWS - 6, T1_COLS - 4, 2, 2);
    if (panel == NULL) {
        curs_set(1);
        endwin();
        delscreen(scr);
        fprintf(stderr, "t1_ncursesw: newwin failed\n");
        return 4;
    }
    box(panel, 0, 0);
    wattron(panel, A_BOLD);
    mvwaddstr(panel, 2, 2, T1_GREETING);
    wattroff(panel, A_BOLD);
    mvaddstr(T1_ROWS - 2, 2, T1_STATUS);
    refresh();
    wrefresh(panel);

    for (;;) {
        ch = getch();
        if (ch == ERR) {
            curs_set(1);
            echo();
            endwin();
            delscreen(scr);
            fprintf(stderr, "t1_ncursesw: getch returned ERR (input closed)\n");
            return 5;
        }
        if (ch == 'q') break;
    }

    delwin(panel);
    curs_set(1);   /* ensure cnorm (\033[?25h) is emitted before rmcup */
    echo();
    endwin();      /* emits rmcup (\033[?1049l) for xterm-family terminfo */
    delscreen(scr);
    return 0;
}
