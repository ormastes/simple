# Stage-4 seed-compiled full CLI: run/test SIGSEGV at startup (Windows branch on Linux, tagged-value deref)

- **ID:** bootstrap_stage4_seed_compiled_full_cli_run_test_crash_2026-07-20
- **Status:** PARTIALLY FIXED — SIGSEGV closed, /proc/meminfo closed; 2 symptoms still OPEN (see "2026-07-20 follow-up" below)
- **Severity:** critical (single defect now gating the entire self-hosted redeploy)
- **Lane:** seed-compiled stage-4 full CLI (cranelift, core-c-bootstrap runtime lane)

## Context
After peeling five walls (LLVM-less seed, stale archive, sanitize collision,
self-host memory blowup, three backfill-class link defects), stage 4 BUILT
successfully for the first time: 47MB binary, sha256 6d587c4bf68a…, builds in
169s, reports `Simple v1.0.0-beta` with **no seed warning**, warm startup
0.00s/9MB, and `-c "print(1+1)"` → 2 works.

## Symptom
Every `run` and `test` invocation crashes at startup: **SIGSEGV rc=139**,
`SEGV_MAPERR si_addr=0x3c194581` (tagged-value-shaped address deref). Before
the crash the binary takes the **Windows platform branch on Linux** and fails
reading `/proc/meminfo`. The `simple_seed` delegate does not rescue it.

Smoke matrix: strictly worse than seed on all 9 specs (every one SIGSEGV vs
seed's mixed pass/fail/timeout baseline) → deploy refused by the
extended-smoke rule; deployed seed left untouched.

## Repro
`/tmp/wt_deploy/build/bootstrap/full/x86_64-unknown-linux-gnu/simple run <any.spl>`
(worktree kept with all native objects, logs in `stage4-seed-build.log`,
`smoke_new/`).

## Leads (in suggested order)
1. Platform-detection marshaling on the core-c lane: the Windows-branch-on-Linux
   selection suggests an extern returning a corrupted value at startup —
   check `rt_env_get` / `rt_file_read_text` value marshaling on the
   core-c-bootstrap lane first (same class as prior EXTERN_DISPATCH landmines).
2. The si_addr looks like a tagged value dereferenced as a pointer — consistent
   with a boxed/tagged return being passed unadapted across the C boundary.
3. gdb with the kept native objects in /tmp/wt_deploy.

## Cannot-adjudicate note
Fat32Core.new abort and REQ-015 (font_renderer TTF crash/timeout) remain
un-adjudicated on self-hosted until this startup crash is fixed.

## 2026-07-20 follow-up: SIGSEGV boundary fixed; 3 startup symptoms triaged

The original SIGSEGV (rc=139, tagged-value deref) is a SEPARATE, already-fixed
issue: commit `d0d471ea1bb` (suffix-boundary mangling fix) plus the earlier
`2e293066315` (`rt_process_run_inherit` missing from
`process_c_runtime_arg_indices` in `compiler/src/codegen/instr/calls.rs`)
closed it — the binary no longer crashes at startup. What remained were 3
non-crashing startup symptoms, root-caused as follows:

**PRIME SUSPECT AUDIT (arg-index tables): no missing entries found.** The
task hypothesis was that more C-runtime externs were missing from
`process_c_runtime_arg_indices`/`text_arg_indices`/`text_cstr_arg_indices`
in `calls.rs` (same class as the `rt_process_run_inherit` fix). Audited
`rt_env_get`, `rt_process_run`, `rt_file_exists`, `rt_file_read_text`,
`rt_dir_list` against their C/Rust signatures — all correctly marshal args
(confirmed empirically via `probe_io.spl` run on both seed and stage4). The
actual recurring defect class this session hit, three separate times, was
**duplicate runtime implementations across build lanes silently diverging**,
not arg-marshaling:
1. `rt_file_read_text` — a Rust impl (`runtime/src/value/sffi/file_io/file_ops.rs`)
   AND a C impl the core-c-bootstrap lane actually links
   (`runtime_native.c` → `spl_file_read` in `runtime_legacy_core.c`), both
   independently buggy the same way (see fix below).
2. `detect_platform()` — 11 separate definitions across the tree (mostly
   unrelated modules with the same generic name); confirmed via
   `nm`/`objdump` that `system_monitor.spl`'s `is_windows()` calls the
   correctly module-qualified `nogc_sync_mut__test_runner__system_monitor__detect_platform`
   (no collision at the call site) — ruled out as symptom #2's cause, but
   the pattern is a standing landmine worth a repo-wide audit.
3. `rt_array_copy` — Rust impl takes a tagged `RuntimeValue`; a SEPARATE
   pure-Simple `simple_core`/`core_array_ops.spl` impl takes a raw `i64`
   with its own tag scheme. Disassembly of the stage4 binary confirmed the
   Rust one is what's actually linked for this build, so this specific
   mismatch is NOT symptom #3's cause, but it's the same "two
   implementations of one extern name" shape and is a landmine for any
   future runtime-bundle switch.

### Symptom 1 — `[MEM] START: (could not read /proc/meminfo)` — FIXED

Root cause: both `rt_file_read_text` (Rust) and `spl_file_read` (C, the one
the core-c-bootstrap lane stage4 actually links — confirmed via
`nm`/`objdump`: `rt_array_copy` resolves to the Rust `simple_runtime` crate,
but `rt_file_read_text`'s C sibling in `runtime_native.c` delegates to
`runtime_legacy_core.c`'s `spl_file_read`, not the Rust crate) sized their
read buffer from `stat()`/`fseek(SEEK_END)+ftell()` reported length.
Pseudo-filesystems (procfs, sysfs) report length 0 for files that generate
content on read, so the 0-byte buffer made a trivially-succeeding zero-byte
read look like a real (empty) result instead of failing loudly.

Fix (commit `dfcf5fc337b`): both implementations now read to EOF into a
growable buffer (`Vec`/`read_to_end` in Rust; a doubling `malloc`/`realloc`
loop keyed on `fread()==0` in C), sizing the result from bytes actually
read. General fix (not meminfo-specific) — audited `rt_file_read_bytes` /
`rt_file_read_lines`, both already EOF-based (`std::fs::read`/
`read_to_string`), not affected by this bug.

Verified: `simple test test/01_unit/compiler/bdd_truthy_runtime_spec.spl`
on a from-scratch-rebuilt stage4 binary (seed cargo-rebuilt +
`native_cache_seed4`/`native-objects-*` caches fully cleared, full 1371/1371
recompile, 0 cached) now prints `[MEM] START: MemAvailable: 96748296 kB`
instead of `(could not read /proc/meminfo)`.

Residual, not chased further: `simple run probe_io.spl` (as opposed to
`simple test ...`) still shows `meminfo_len=0` on the stage4 binary even
after this fix, while the seed binary correctly shows 1532 — `run` appears
to exercise a third code path distinct from both the C lane and the
directly-tested Rust lane. Out of scope since the task's actual symptom
(from `simple test`) is confirmed fixed.

### Symptom 2 — Windows platform branch chosen on Linux — STILL OPEN

`ensure_kill_monitor_running()` in
`src/lib/nogc_sync_mut/test_runner/system_monitor.spl` takes the
`is_windows() and not is_mingw_or_msys()` branch and prints
`WARNING: scripts/resource/kill_simple_monitor.bat not found` on a Linux
host with no `OS`/Windows-flavored env vars set.

Ruled out: `nm`/`objdump` on the stage4 binary shows `is_windows()` calling
the correctly module-qualified `detect_platform()` (no name collision at
the call site, despite 11 same-named `detect_platform` functions existing
across the tree — symbol mangling disambiguates by module path correctly).
`rt_env_get`/`rt_process_run` (the externs `host_os()`/
`_is_windows_platform()` depend on) marshal correctly in isolation per the
arg-index audit above.

Not yet resolved: instrumented builds (print statements added directly in
`is_windows()`/`detect_platform()`/`_is_windows_platform()`, each requiring
a full stage4 rebuild to observe) showed `_platform_detected=false` and
`_platform_windows=false` both immediately before AND after the
`detect_platform()` call, with `detect_platform()`'s own top-of-body print
never firing — yet the runtime branch taken behaves as if the overall
`is_windows() and not is_mingw_or_msys()` condition is true. This is
inconsistent with the printed operand values and was not reconciled within
this session's budget. Candidate for further investigation: boolean
short-circuit (`and`/`not`) lowering for two function-call operands, or
module-global write/read visibility across function boundaries in this
specific compiled context. Needs cranelift IR-level debugging (MIR dumps
or gdb), not print-based tracing, to pin down.

### Symptom 3 — `Test discovery found 0 test files` despite the file existing — STILL OPEN

`bin/simple test test/01_unit/compiler/bdd_truthy_runtime_spec.spl` (and
`--refresh-manifest`) reports 0 files discovered even though
`count_spec_files_on_disk` (a separate, string-only check) confirms 1
`_spec.spl` file exists on disk.

Precisely localized via per-branch instrumentation (each iteration required
a full stage4 rebuild): `discover_test_files_fast()` in
`src/lib/nogc_sync_mut/test_runner/test_runner_files.spl` correctly
computes and returns a 1-element array (`file_exists=true`,
`is_test_file=true`, `file_has_pending_tag=false`, confirmed via a print
right at the `return [base_path]` site: `len=1`). The caller
(`run_tests()` in `src/app/test_runner_new/test_runner_main.spl`) receives
it correctly too (`all_files.len()=1` immediately after the call, and still
`1` after `validate_system_test_covers(all_files)`). The corruption is
isolated to ONE specific statement: `var files = all_files` (line 179) —
immediately after this line, `files.len()=0` while `all_files.len()=1`
(the untouched source) remains correct.

This statement is exactly the pattern fixed by commit `8cccc7b70bc`
("fix(seed): copy array on local-bind place-read to stop JIT alias
bypass") — a `var c = arr` place-read now inserts an `rt_array_copy(vreg)`
call (`compiler/src/mir/lower/lowering_stmt.rs`,
`is_array_place_alias`/`hir_expr_is_place`) instead of aliasing the heap
handle. Investigated and ruled out as the failure site itself:
- `is_array_place_alias` correctly evaluates true for this call (place-read
  of an existing `[text]`-typed local, not `[u8]`).
- `rt_array_copy`'s Rust implementation
  (`runtime/src/value/collections.rs:2847`) is correct (allocates a new
  array of the same length, copies every element) — verified via
  `nm`+`objdump` on the stage4 binary: the linked `rt_array_copy` calls
  real `simple_runtime::value::heap::get_typed_ptr` /
  `simple_runtime::value::collections::array_data_layout` symbols from the
  freshly-built Rust crate, not a stale or alternate implementation.
- Ruled out `emit_union_wrap_if_needed`/`emit_unit_bound_check` (the two
  transforms applied to the copy result before the `Store`) — `files`'s
  declared type is a plain `[text]` array, not a union or unit type, so
  both are no-ops here.

Root mechanism not pinned within this session's budget. Leading
candidates for a follow-up: the value/vreg passed to the inserted
`rt_array_copy` call not carrying the tag/liveness info the callee needs
to recognize it as a valid `Array`-typed `RuntimeValue` in this specific
compiled context (large function, many locals/branches) — but this is a
hypothesis, not confirmed. Needs cranelift MIR dump comparison (with vs.
without the `is_array_place_alias` fix) to localize precisely; print-based
tracing bottomed out at "the copy result reads empty" without reaching the
why.

### Not committed
No fix was attempted for symptoms 2 or 3 — per repo rule, no speculative/
workaround fixes without a confirmed root cause. Both are precisely
localized (call sites, exact statements, ruled-out candidates) for the next
session to pick up with cranelift IR-level tooling.
