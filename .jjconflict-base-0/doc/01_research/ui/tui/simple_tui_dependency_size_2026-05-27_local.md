<!-- codex-research -->
# Simple TUI Dependency Size Domain Research

Date: 2026-05-27

## External Baseline

Small terminal apps can be built with POSIX terminal mode control plus direct
escape sequences. That keeps the runtime shape close to libc plus the dynamic
loader. Curses/ncurses adds useful terminal portability and capability database
handling, but it is a larger abstraction layer than a fixed ANSI/termios lane.

Relevant references:

- POSIX terminfo describes terminal capabilities as data used by curses-style
  APIs: https://pubs.opengroup.org/onlinepubs/7908799/xcurses/terminfo.html
- ncurses documentation describes terminal database lookup and terminfo/termcap
  behavior: https://manpages.debian.org/bookworm/ncurses-doc/ncurses.3ncurses.en.html
- xterm documentation covers control/escape sequence behavior used by direct
  terminal rendering paths: https://man.archlinux.org/man/xterm.1.en

## Implication For Simple

For a C-like small TUI target, Simple should preserve a direct terminal capsule:

- terminal mode setup
- alternate screen enter/leave
- cursor movement
- clear/redraw
- bounded input loop

Higher-level portability, terminal databases, widgets, shared UI, GUI/web
bridges, async runtimes, TLS, HTTP, compression, and filesystem preload should
remain opt-in capsules. This mirrors the C distinction between a tiny
termios/ANSI program and a richer curses-style application.

## Decision Bias

Dependency refactoring is the correct next step. A bottom-up rewrite is only
justified if the narrow direct-terminal capsule cannot remain isolated.
