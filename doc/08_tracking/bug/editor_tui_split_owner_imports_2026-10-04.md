# Editor TUI split modules omit their declaration owners

The native early Phase4 run targeting `9d484080c34c6e52ea001c5231c0f62bc0e383ea`
with producer `0fce5d949d48b1a924c8131cc496ec191c8fce43033dbdc793386d819cc61e99`
records 21 HIR errors in `app/editor/tui_shell_panels.spl` (10 shown), including
unresolved `EditorController`, `LayoutZones` and `SplitRect`. The shell separately
records an unresolved `md_stats_to_status_bar`. Evidence is the retained
`early-p4-full-cli-9d484/hir-first-failures.grouped.json`, bound to live-prefix
SHA-256 `ec72c4fb523a9323230bc1982b3984c1d0c884703551d60b14c0db23dbc6e06c`.
These are module failures, not executed tests; the cohort was still running at
the observation.

The declarations exist. The panel module was split from the shell without
importing controller/layout/buffer/split-tree/preview/outline owners, while the
shell uses the Markdown statistics formatter without importing its service.
Add explicit imports of those existing nominal types and functions. No duplicate
types, placeholder functions, visibility widening or behavior substitution is
introduced. The production delta contains imports only.

Four executable regressions import the affected modules and exercise real group
lookup (IDs differ from indices, missing and empty groups) and buffer-backed
semantic-token rendering (plain and styled output). They open no terminal or
window. All four are UNRUN; full TUI native qualification is still pending.

Other failures are separate. GUI shell/SDL bridge shared types and GUI helper
owners need their own repair. The panel's existing reverse call to
`tui_render_editor_line_at_theme` belongs to `app.editor.tui_shell`; it is not
provided by `std.editor.backend.tui_backend`. This checkpoint does not introduce
a circular import to hide that ownership problem. A shared rendering leaf can
remove that pre-existing coupling in a subsequent scoped change.

DrawIR also needs a coherent v4 state contract: the current shared v2 command
lacks the affine/fractional/raster fields expected by newer consumers. A constant
predicate or a guard removal would hide lost semantics. The separate incomplete
DrawIR draft was inspected but left unchanged. T32 and `std.io.stdin_read_line`
export failures likewise remain separate resolver/owner investigations.
