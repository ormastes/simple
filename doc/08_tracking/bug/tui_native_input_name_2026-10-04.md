# TUI native input name

Status: source repair prepared; native compile and piped-input checks pending.

The frozen Windows Phase4 cohort from source `9737d1217bc4`, produced by
Cranelift Phase2 SHA `776ce2a1b8b0f92d44e5dd70b5fac365ba96187f76cfa0ffc2c5bdcac8fdae40`,
reports an unresolved `input` name in `src/app/ui.tui/app.spl` and
`src/app/ui.tui/input.spl`.

Both TUI stdin owners now call the existing `std.io.stdin_read_line` facade.
It preserves the empty prompt, EOF-to-empty behavior and trimming. It adds no
raw runtime extern or alternate stdin implementation. This does not qualify
the unrelated async route or any other GC/async configuration.

Compile `test/04_smoke/tui_stdin_read_line.spl` and
`test/04_smoke/tui_input_stdin_read_line.spl` with the corrected source and
run its real binary with `  hello  ` plus LF, the same bytes plus CRLF, and
empty input. Require exit 0 and exact `value=hello`, `value=hello`, and `value=`
lines respectively, with empty stderr. Retain build/run receipts; this report
and the fixture alone are not a runtime PASS.
