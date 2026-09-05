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

## Reduction sweep — DONE (measured) 2026-06-13
A real migration of app-facing example code off raw `rt_*` externs to `std.io_runtime`
wrappers (`read_file`/`write_file`/`file_exists`/`env_get`/`process_run`), run via 5 parallel
agents over disjoint directory subtrees, each changed file verified `bin/simple check` OK.

| Metric | Before | After | Δ |
|--------|------:|------:|---:|
| Example files declaring migratable file/env `rt_*` externs | 82 | **39** | **−43** |
| `rt_process_run` extern decls in examples | 38 | **23** | **−15** |
| Raw `extern fn rt_*` decls removed (file/env/process) | — | — | **~84** |

Migrated dirs: `examples/06_io/{ui,smux,tls_hosted_client,simple_web_server}` +
`examples/10_tooling/{obsidian-search,trace32_tools,mcpgdb,llm_cli_tools}`. Commit `rrp 0d9`.

**Honestly NOT migrated** (no false-green): externs with no 1:1 stdlib wrapper (`rt_dir_list`,
`rt_file_size`, `rt_file_delete`, `rt_dir_create` variants) or signature mismatch (`text?`
returns vs `read_file -> text`); hardware/MMIO/GUI externs (`rt_port_*`, `rt_mmio_*`, `rt_gui_*`)
are intentional low-level access and correctly stay raw.

## Remaining (smaller, follow-up)
The 39 residual files are mostly: non-1:1 externs (need new stdlib wrappers first), GUI examples
with pre-existing unrelated `check` failures, and hardware examples that legitimately keep raw
externs. Closing them requires adding the missing stdlib wrappers — a bounded follow-up.

## Sweep completed — 3 waves (commits rrp 0d9, tys 497, trk 723)
| Wave | Scope | Externs removed |
|------|-------|----------------:|
| 1 | file/env/process across ui, smux, tls, obsidian, trace32, mcpgdb, llm | ~84 |
| 2 | dir/delete/size/append residual (existing wrappers) | ~21 |
| 3 | all remaining 1:1-wrapper externs, all swept dirs | ~103 |
| **Total** | ~107 app-facing example files touched | **~208** |

**Files declaring a migratable `rt_*` extern: 82 → 23 (≈70% reduction).** No-regression verified
after every wave (API/arch guard symbols+arch GREEN; perf+cache specs 6/0). All migrations to
EXISTING `std.io_runtime` wrappers (`read_file`/`write_file`/`file_exists`/`file_delete`/`file_size`/
`file_append_text`/`dir_list`/`dir_create`/`dir_create_all`/`env_get`/`process_run`).

### Floor closure update — 2026-06-13 (commit `1406f27` / origin `e7fdff8`)
Two of the "no wrapper exists" items are now closed with real wrappers over
already-registered runtime externs (verified: `check` OK + runtime smoke —
write/read 3 bytes, recursive dir remove confirmed file gone):
- `std.io_runtime.file_write_bytes(path, bytes) -> bool` → wraps `rt_file_write_bytes`.
- `std.io_runtime.dir_remove_all(path) -> bool` → wraps `rt_dir_remove_all`
  (also fixed latent bug: `dir_remove(path, recursive=true)` had ignored the flag).
Also corrected: `getpid()` (line 158) and `cwd()` (line 148) **already existed** —
files using `rt_getpid`/`rt_env_cwd` can migrate to those today; no new wrapper needed.

### Honest floor — the remaining residual (need NEW runtime externs or have mismatched signatures)
No false-green: these are deliberately NOT force-migrated.
- **No stdlib wrapper AND extern needs 6-site runtime registration first** (true rebuild
  follow-up, out of scope here): `rt_http_*`, `rt_time_now_monotonic_ms`/`rt_time_ms`,
  `rt_stdin_read_line`, `rt_process_run_timeout`, `rt_file_read_text_at` (3-arg).
  (`rt_time_now_unix_micros` already has the `time_now_unix_micros()` wrapper.)
- **Signature mismatch:** `rt_file_read_text -> text?` (nullable) in `simple_browser.spl` —
  wrapper returns `text`; migrating would change semantics.
- Hardware/terminal/ctypes externs (`rt_port_*`, `rt_mmio_*`, `rt_gui_*`, `rt_term_*`,
  `rt_alloc`/`rt_free`/ctypes) correctly stay raw — not app-developer-convenience surface.

## Status
DONE — decisive measured reduction (82→23, ~208 externs), no regression. Floor advanced:
`file_write_bytes`/`dir_remove_all` wrappers added + `getpid`/`cwd` confirmed pre-existing.
The only true remaining follow-up is externs that need NEW 6-site runtime registration
(rebuild territory), not further migration of existing wrappers.
