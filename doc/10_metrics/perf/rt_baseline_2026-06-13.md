# `rt_*` App-Developer-View Baseline (AC-9) — 2026-06-13

Baseline "before" count for the AC-9 goal: *reduce/eliminate app-developer-visible `rt_*` usage*
by pushing optimizations behind stdlib/public APIs. The **reduction sweep itself is STAGED** (P1
SG-1.2); this doc only captures the measurement to diff against.

## Raw counts (grep `rt_[a-z_]*`)
| Scope | Count | Notes |
|-------|------:|-------|
| `examples/**.spl` call sites (raw) | **3225** | app-developer view; OVERCOUNTS — see caveat |
| `src/lib/nogc_async_mut/**` `extern fn rt_*` decls | **118** | default-tier runtime surface |

## Top raw hits (examples/)
`rt_name` 200 · `rt_port_outb` 154 · `rt_file_read_text` 129 · `rt_process_run` 122 ·
`rt_gui_set_text_buf` 119 · `rt_env_get` 119 · `rt_tok` 109 · `rt_file_exists` 98 ·
`rt_test` 82 · `rt_put` 72 · `rt_file_write_text` 72 · `rt_mmio_write_u` 59 · `rt_col` 56 · `rt_h` 50

## Caveat (measurement quality)
The raw grep matches any `rt_`-prefixed identifier, so it includes **false positives** that are
local variables/fields, not runtime externs: `rt_name`, `rt_tok`, `rt_line`, `rt_col`, `rt_put`,
`rt_h`, `rt_test` are almost certainly local idents (e.g. `rt` = a struct named `rt`). The genuine
app-facing runtime externs are: `rt_port_outb`, `rt_file_read_text`/`_write_text`/`_exists`,
`rt_process_run`, `rt_gui_set_text_buf`, `rt_env_get`, `rt_mmio_write_u`. A refined count (the first
step of the AC-9 sweep) must filter to actual `extern fn rt_*` declarations + their resolved call
sites, not the raw prefix.

## Next step (staged — AC-9 SG-1.2)
1. Refined measurement: resolve true `rt_*` extern call sites in app-facing code (exclude local idents).
2. Wrap the high-frequency genuine externs (`rt_file_*`, `rt_process_run`, `rt_env_get`,
   `rt_gui_set_text_buf`) behind stdlib public APIs so example/app code calls the stdlib, not `rt_*`.
3. Re-measure; record before/after in this table.

## Status
OPEN — baseline captured; reduction sweep staged.
