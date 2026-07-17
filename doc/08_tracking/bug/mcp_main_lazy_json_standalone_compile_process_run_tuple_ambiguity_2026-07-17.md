# main_lazy_json.spl standalone-compile: `process_run`'s unlabeled (text, text, i64) return trips a standalone-only tuple-ambiguity check

**Status:** FIXED 2026-07-17 (Worker S) — see "Resolution" section at the end.

**Date:** 2026-07-17
**Scope:** `src/app/mcp/main_lazy_json.spl` (standalone-compile only); root
cause is `std.io_runtime.process_run` / `std.nogc_sync_mut.io.process_ops.process_run`'s
signature, both out of scope for this lane (`src/app/mcp/**` only).
**Severity:** low — does not affect the real server (full `main.spl` compiles
and runs fine); only affects standalone `simple compile
src/app/mcp/main_lazy_json.spl` used by ad hoc per-file sweeps/bisection.

## Symptom

```
timeout 300 src/compiler_rust/target/bootstrap/simple compile \
  src/app/mcp/main_lazy_json.spl -o /tmp/probe.smf
```

fails with:

```
error: compile failed (src/app/mcp/main_lazy_json.spl): semantic:
src/app/mcp/main_lazy_json.spl: Other("anonymous multi-return tuple contains
repeated field types; add labels to disambiguate")
```

## Root cause

`std.io_runtime.process_run(cmd, args) -> (text, text, i64)` (stdout, stderr,
exit code) has two unlabeled `text` fields. Merely importing and calling this
function is enough to trip a standalone-compile-mode type-ambiguity check —
confirmed with a 5-line minimal repro (`use std.io_runtime.{process_run}` +
one call + `.0` field access, no destructuring, no other code) that fails
identically. The same call graph compiles cleanly as part of the full
`src/app/mcp/main.spl` program (`simple compile src/app/mcp/main.spl`
succeeds, `EXIT=0`, verified before and after this doc's other fixes) — the
ambiguity check appears to be standalone/entry-file-specific, not something
that fires during the real whole-program build.

Originally suspected as a `main_lazy_json.spl`-local issue (the file used
`(stdout, stderr, code) = process_run(...)` 3-way destructuring assignment in
`shell_cmd`/`_mcp_detect_shell`/`strip_ansi`); rewritten to indexed field
access (`.0`/`.1`/`.2`, avoiding both this and the file's own documented
"`val (a,b) = expr` is broken in interpreter" landmine) as a genuine cleanup,
but the standalone-compile error persisted afterward — proving the
destructuring style was never the actual cause. Confirmed via the minimal
repro above that the error comes from `process_run`'s own declared return
type, not from how the caller consumes it.

## Why not fixed here

Fixing this at the root means labeling `process_run`'s return tuple (e.g.
`-> (stdout: text, stderr: text, code: i64)`) in
`src/lib/nogc_sync_mut/io_runtime.spl` and/or
`src/lib/nogc_sync_mut/io/process_ops.spl` — both widely-shared stdlib files
used across the entire codebase (dozens of callers via `app.io.mod`), well
outside this lane's scope (`src/app/mcp/**` + `test/**` + bug docs only).
Also unclear whether unlabeling would break any of the many existing
positional-tuple call sites elsewhere. Flagged as a known, narrow,
low-impact standalone-compile-only limitation for whoever next touches
`process_run`'s signature or the standalone-compile-mode tuple-ambiguity
checker.

## Impact

None on the running server (the file only ever loads as part of the real
`main.spl`/`main_dispatch.spl` import graph, which compiles and — modulo the
separately-filed
`mcp_stdio_smoke_seed_flat_registry_len_i64_2026-07-17.md` runtime defect —
runs). Only affects ad hoc standalone `simple compile` invocations of this
one file, e.g. a future lazy-module compile sweep.

## Files changed here (real fixes, unrelated to the above open item)

- `src/app/mcp/main_lazy_diag_tools.spl`: added
  `use .main_lazy_query_tools.{_mcp_find_simple_binary}` — was calling an
  undefined identifier when compiled standalone (this exact gap was
  previously reported fixed in an earlier session but was not present on
  disk; re-applied).
- `src/app/mcp/main_lazy_vcs_tools.spl`: added
  `use .main_lazy_json.{make_tool_result, shell_cmd, extract_field}` — same
  missing-sibling-import pattern (this was the "KNOWN OPEN sibling gap"
  flagged in this session's task guide; no prior bug doc existed for it,
  filed and fixed together here).
- `src/app/mcp/main_lazy_protocol.spl`: added
  `use std.io_runtime.{file_read}` and
  `use .main_lazy_json.{make_json_result, make_error, extract_field,
  escape_json, top_level_item_count, shell_cmd, _slice_text}`; fixed a
  latent `NL` → `_PROTO_NL` typo (the file already defines `_PROTO_NL =
  "\n"` locally but one call site referenced the undefined bare `NL`,
  which only happened to resolve when compiled as part of `main.spl`,
  which separately defines its own `NL`). Explicit imports were also tried
  as a (disproven) hypothesis for fixing the separately-filed runtime
  registry-corruption defect — they fix the standalone-compile gap but do
  **not** fix the runtime defect (verified: identical crash before/after).
- `src/app/mcp/main_lazy_json.spl`: exported `make_json_result`, `make_error`,
  `extract_field`, `escape_json`, `top_level_item_count`, `shell_cmd`,
  `_slice_text` (previously locally-defined but not exported); rewrote
  `shell_cmd`/`_mcp_detect_shell`/`strip_ansi`'s 3-way `process_run(...)`
  destructuring assignments to indexed field access (`.0`/`.2`) — a genuine
  cleanup avoiding the file's own documented interpreter-destructuring
  landmine, though it did not resolve this doc's own standalone-compile
  issue (root cause is upstream, see above).

All four files' standalone `simple compile` now succeeds; `main.spl`'s full
compile was re-verified clean (`EXIT=0`) after every edit in this list.

## Resolution (Worker S, 2026-07-17)

**Mechanism:** the standalone-compile-mode ambiguity check fires on the
*declared return type* of any function whose result an entry file accesses
by field index or destructures, when that type is an unlabeled tuple with
repeated field types — not merely on the underlying `extern fn` it wraps.
Confirmed via isolated probes: an `extern fn rt_process_run(...) -> (text,
text, i64)` combined with a *labeled* wrapper `pub fn process_run(...) ->
(stdout: text, stderr: text, exit_code: i64): rt_process_run(cmd, args)`
compiles standalone cleanly, and both existing call styles keep working
against the labeled type — indexed access (`.0`/`.1`/`.2`) and 3-way
destructuring (`val (a, b, c) = process_run(...)`) both still compile and
return the same values at runtime as before labeling.

**Chosen path:** neither of the two options this bug originally sketched
(struct-migrate all callers, or add a parallel struct-returning function).
Caller census: `use std.io_runtime` import lines that also reference
`process_run` appear in **~150 files** across `src/` and `test/` (far above
the guide's <15 threshold for a mechanical struct migration, and adding a
parallel `process_run_result` API would have left permanent dual-API debt
for a class of bug the labels below fix everywhere at once). Instead this
is a **true root fix**: `src/lib/nogc_sync_mut/io_runtime.spl`'s
`pub fn process_run` return type was changed from
`-> (text, text, i64)` to `-> (stdout: text, stderr: text, exit_code:
i64)`. Zero caller changes were required anywhere in the repo — the label
alone clears the standalone-compile ambiguity check for every module that
imports `process_run` from `std.io_runtime`, not just
`main_lazy_json.spl`.

**One caveat found in the process:** *named* field access on the labeled
tuple (e.g. `result.stdout`) works under direct interpreter `run` but fails
under the test-runner's execution path with `semantic: undefined field:
unknown property or method 'stdout' on Tuple`. No current caller uses named
field access on `process_run`'s result (all ~150 use `.0`/`.1`/`.2` or
destructuring), so this doesn't block anything, but it's a real
inconsistency across execution paths for labeled-tuple field access worth
flagging for whoever next works on the interpreter/test-runner value
representation for labeled tuples — not fixed here (out of this lane's
scope; no Rust changes made per this lane's hard rules).

**Verification:**
- `timeout 300 src/compiler_rust/target/bootstrap/simple compile
  src/app/mcp/main_lazy_json.spl -o probe.smf` → now compiles cleanly
  (`Compiled ... -> probe.smf`), no error at all (not even a residual
  different limitation).
- `timeout 300 src/compiler_rust/target/release/simple check
  src/app/mcp/main.spl` → `All checks passed (1 file(s))`, exit 0.
- New regression spec `test/01_unit/lib/io_runtime/process_run_result_spec.spl`
  (indexed-access + destructuring + nonzero-exit-code cases) → `3 examples,
  0 failures` via `timeout 240 src/compiler_rust/target/release/simple test
  <spec>`.
- Spot-checked 5 other real callers of `std.io_runtime.process_run`
  (`src/app/cli/theme_sync.spl`, `src/compiler/70.backend/linker/linker_wrapper_helpers.spl`,
  `src/lib/nogc_sync_mut/package/installer/tool_detect.spl`,
  `src/app/simple_lsp_mcp/tools.spl`) with `simple check` — all still pass
  (one other file, `src/app/mcpgdb/main.spl`, fails standalone `check` on an
  unrelated pre-existing `export use module.*` wildcard error in a
  different transitive module, confirmed present before this change too via
  a scoped revert-and-retest).

**Not touched:** `std.nogc_sync_mut.io.process_ops.process_run` (a
separate facade, not `std.io_runtime`'s owner file, and not imported by
`main_lazy_json.spl`) has the identical unlabeled-tuple shape and likely the
same standalone-compile limitation. Left as-is — out of this lane's scope
(only `std.io_runtime`, the facade actually named in this bug's repro, was
in scope). Flagging here so it isn't silently forgotten if someone next
hits a standalone-compile failure through that module instead.
