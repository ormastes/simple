# Bug: check-simpleos-wm-qmp-drag-delta-evidence.shs invokes a nonexistent entry file

- **Date:** 2026-07-02
- **Severity:** medium (gate cannot run at all)
- **Area:** scripts/check/check-simpleos-wm-qmp-drag-delta-evidence.shs

## Symptom
The gate runs `bin/simple run simpleos_desktop_qmp_launch_root.spl`, but no file
with that name exists anywhere in the repo, so the gate fails unconditionally.
Reproduced on macOS host 2026-07-02, independent of any local changes.

## Expected
The gate should invoke the actual QMP launch entry (see
`src/app/test/simpleos_desktop_qmp_launch.spl` and the
`_wm_simple_web_qmp_capture_target()` flow) or the missing root wrapper should
be restored. Likely a casualty of an entry-file rename/move.

## Root cause (confirmed via git history)
Commit `22ae57646c` ("test(gui): prove wm qmp drag delta failure", 2026-06-11)
added a one-off scratch file `simpleos_desktop_qmp_launch_root.spl` at the repo
root and repointed the gate at it (it previously correctly ran
`src/app/test/simpleos_desktop_qmp_launch.spl`, same as it was originally
authored in `0c3d112f38`). Commit `a463cbcd29` ("chore: prune top-level
scratch/probe files from origin/main") later deleted that root-level scratch
file as janitorial cleanup, but nobody repointed the gate back to the real
entry — leaving it broken exactly as described above. The sibling gate
`scripts/check/check-qemu-gtk-wm-capture-evidence.shs` (line ~289) never had
this problem; it has invoked `src/app/test/simpleos_desktop_qmp_launch.spl`
all along and was used as the reference idiom for the fix.

## Fix applied (2026-07-02)
`scripts/check/check-simpleos-wm-qmp-drag-delta-evidence.shs` line 193 changed:
```
-    "$SIMPLE_BIN" run simpleos_desktop_qmp_launch_root.spl --mode=interpreter --clean >"$LAUNCH_OUT" 2>&1
+    "$SIMPLE_BIN" run src/app/test/simpleos_desktop_qmp_launch.spl --mode=interpreter --clean >"$LAUNCH_OUT" 2>&1
```
This one-line change restores parity with the sibling gate and is verified
correct by git history (it reverts exactly what `22ae57646c` broke). No other
lines in the gate script needed to change — the field-parsing (`launcher_*`,
QMP socket wait, HMP drag injection, region-diff pass/fail thresholds) all
already matches what `src/app/test/simpleos_desktop_qmp_launch.spl`'s
`main()` prints (`simpleos_desktop_qmp_status`, `_reason`, `_target`,
`_entry`, `_pid`, `_socket`, `_serial_log`, `_stderr_log`, `_marker_state`).

## Further breakage discovered during end-to-end verification (NOT fixed — separate, deeper bug)
Running the fixed gate on this macOS (aarch64) host with
`bin/release/aarch64-apple-darwin-macho/simple` (built 2026-06-06) does not
reach a pass: `bin/simple run src/app/test/simpleos_desktop_qmp_launch.spl`
itself exits 1 with **zero stdout output** (not even the very first
`simpleos_desktop_qmp_*` field, and not even a `print` placed as the first
statement of `main()`) — `main()` is never reached at all. This is unrelated
to the entry-path bug above; it reproduces identically for
`--mode=interpreter` and for `SIMPLE_EXECUTION_MODE=interpret` (the latter at
least avoids a secondary, separate JIT crash: `--mode=interpreter` alone lets
the driver attempt a JIT compile first, which panics with `can't resolve
symbol rt_any_add` inside `cranelift_jit::backend::JITModule::get_address`
before falling back — crash reports at `.simple/logs/crash_{57311,97179,97171,53803}.log`).

Root cause isolated by bisection (minimal repro files kept only in scratch,
not committed): the launch entry's `use app.io.mod.{...}` import is the
culprit, and within `app.io.mod` (`src/app/io/mod.spl`) it traces specifically
to:
```
use app.io.cli_ops.{get_args, exit, cli_get_args, cli_exit, cli_file_exists}
use app.io.cli_ops.{cli_read_file, context_generate, context_stats, context_index_packs, context_query_index, context_sql_index_packs, context_sql_query_packs, context_sql_query_packs_by_source, settlement_main}
use app.io.cli_ops.{fault_set_stack_overflow_detection, fault_set_max_recursion_depth}
use app.io.cli_ops.{fault_set_timeout, fault_set_execution_limit}
```
A standalone probe file containing only these four `use app.io.cli_ops.{...}`
lines plus a trivial `fn main(): print "OK"; 0` reproduces the exact same
silent exit-1-before-main failure under `SIMPLE_EXECUTION_MODE=interpret`.
`app.io.cli_ops.spl` re-exports `context_generate`/`context_stats`/etc. from
`app.io.context_ops` (line 255: `export use app.io.context_ops.{...}`), and
loading that chain also emits
`[gc-warning] Higher-layer module 'std.nogc_sync_mut.daemon_sdk.types' (family: nogc_sync_mut) imported in restricted context (family: nogc_async_mut) (higher_layer_runtime_family)`
— pointing at the RAG/context-index/settlement/daemon_sdk dependency chain
pulled in by `context_ops` as the likely proximate cause of the module-load
failure. By contrast, isolated tests of every OTHER submodule re-exported by
`app.io.mod` (`file_ops`, `dir_ops`, `process_ops`, `time_ops`,
`sysinfo_ops`, `debug_stubs`, `os.qemu_runner`, `app.io.env_ops`) load and run
fine individually.

Because `app.io.mod` is a widely used shim (`use app.io.mod.{...}` /
`use app.io.{...}`), this almost certainly also blocks
`scripts/check/check-qemu-gtk-wm-capture-evidence.shs`, which invokes the same
`src/app/test/simpleos_desktop_qmp_launch.spl` entry and has had the correct
path all along — i.e. that gate is likely equally broken on this host/binary,
just not via a wrong-path symptom.

This is a pre-existing interpreter/module-loading issue, not something
introduced by the entry-path fix above, and it is not small enough to fix as
part of this task (it sits in shared `app.io.cli_ops`/`app.io.context_ops`
infrastructure and would need real interpreter-level investigation, plus a
bootstrap rebuild+redeploy to verify — out of scope here). Filing as a
follow-up: **the drag-delta gate's entry-path bug is fixed, but the gate still
cannot reach a `pass` end-to-end on this host until the `app.io.cli_ops` /
`app.io.context_ops` module-load failure is fixed separately.**

## Status: 2026-07-02
- Entry-path bug: **FIXED** (`scripts/check/check-simpleos-wm-qmp-drag-delta-evidence.shs` now runs `src/app/test/simpleos_desktop_qmp_launch.spl`).
- End-to-end gate pass: **still blocked**, by the separate `app.io.cli_ops`
  module-load issue above. Evidence of the blocked run: `qemu_wm_drag_delta_status=unavailable`,
  `qemu_wm_drag_delta_reason=wm-qmp-launch-failed`,
  `qemu_wm_drag_delta_guest_input_contract_reason=guest-entry-source-missing`
  (report written to
  `doc/09_report/simpleos_wm_qmp_drag_delta_evidence_2026-07-02.md`, untracked,
  not added to git per repo convention).
