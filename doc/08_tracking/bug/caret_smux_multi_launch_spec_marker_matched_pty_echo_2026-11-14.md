# `caret_smux_multi_launch_spec` read the viewport before the child reported it (2026-11-14)

**Symptom (macOS 26.5 arm64):** "resizes one child's real PTY and the child
observes the new viewport" failed 5/6 with `expected -1 to be greater than 0`,
then `expected false to equal true` and `expected -1 to equal -8` (both
consequences: the resize target was derived from the `-1`).

**Root cause — spec defect, not PTY resize:** the POSIX branch of
`_child_columns` (`test/03_system/app/llm_caret/feature/caret_smux_multi_launch_spec.spl:127`)
sent `echo M<n> && stty size` and waited for the literal `M<n>`. The PTY echoes
the typed command line, so the wait was satisfied by the echo before the shell
had run anything; the screen captured at that moment held only
`echo M61111 && stty size` and no `rows cols` line. The Windows branch already
avoided this by waiting for a computed sum (`set /a n+1`), as the helper's own
comment requires.

**Fix (spec only):** POSIX sends `stty size && echo M$((n+1))` and waits for
`M<n+1>` — text that is absent from the echoed command and is printed after
`stty` answered. Assertions are unchanged; with the race gone the child reports
its width, `smux_resize` returns ok, and the child observes `before - 7`
columns, so `rt_pty_resize` (TIOCSWINSZ) is verified working on macOS.

**Result:** 5/6 -> 6/6 on macOS with the shared seed. No product code changed.
The reproducer is the scenario itself; the nearby case is the same helper's
second call after the resize (`_child_columns(binding, "alpha", 62222)`), which
was racing the same way.
