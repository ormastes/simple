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

## Linux follow-up: 2026-07-02
- Entry path remains fixed and the gate now invokes
  `src/app/test/simpleos_desktop_qmp_launch.spl`.
- The wrapper now distinguishes an empty launcher entry
  (`guest-entry-not-reported`) from a reported path that is missing on disk
  (`guest-entry-source-missing`).
- Live evidence at `build/simpleos-wm-qmp-drag-delta-long/evidence.env` reached
  the real `wm-simple-web` launcher and validated the guest input contract:
  `qemu_wm_drag_delta_guest_input_contract_status=pass`.
- Current blocker is earlier than QEMU drag injection: the self-hosted native
  build of `examples/09_embedded/simple_os/arch/x86_64/gui_entry_engine2d.spl`
  timed out at `900000` ms. The wrapper now reports this as
  `wm-simple-web-build-timeout` instead of the generic
  `wm-simple-web-build-failed` when the launch log contains the native-build
  timeout signature.
- The timed-out command used `--log on`; the QMP wrapper now defaults
  `SIMPLE_OS_LOG_MODE=off` for the launcher, matching the sibling fullscreen
  evidence wrapper for this same kernel while preserving explicit env
  overrides for diagnostics.
- A follow-up live run with the log-off default still timed out before QEMU:
  `build/simpleos-wm-qmp-drag-delta-logoff/evidence.env` reports
  `qemu_wm_drag_delta_reason=wm-simple-web-build-timeout`,
  `qemu_wm_drag_delta_launcher_reason=wm-simple-web-build-timeout`, and
  `qemu_wm_drag_delta_guest_input_contract_status=pass`.
- The failed live runs left orphaned `native_build_worker.spl` processes for
  `build/os/simpleos_wm_simple_web_check_32.elf`. Those stale workers were
  stopped, and the OS runner now passes `--timeout 870` to this target's
  native-build worker so it should report through `simple native-build` before
  the outer 900s OS build timeout kills the supervisor.
- The `wm-simple-web` target source roots were narrowed from
  `build/os/generated`, `src/os`, `src/lib`, and the x86_64 SimpleOS examples
  directory to `build/os/generated`, `src/os`, and the x86_64 examples
  directory. The entry and its direct imports do not use `src/lib`, so this
  avoids loading the broad library tree in the QMP kernel build.
- The `gui_entry_engine2d.spl` entry also dropped dead Engine2D-object helper
  functions and unused Simple Web HTML reads. The active QMP evidence path uses
  direct framebuffer/MMIO panel writers plus the existing serial markers, so
  this reduces the entry module without changing the drag/fullscreen contract.
- Typed integer suffix literals in `gui_entry_engine2d.spl` were normalized to
  plain literals so the self-hosted parser no longer reports local
  `parser_error` diagnostics for the freestanding entry during `bin/simple
  check`.
- A bounded reduced-source native-build probe of the same entry with
  `--source build/os/generated --source src/os --source
  examples/09_embedded/simple_os/arch/x86_64`, `--log off`, and `--timeout 120`
  produced no parser/import/semantic diagnostics before the worker timeout.
  That keeps the current blocker classified as compile-time cost rather than an
  immediate source-root or parser break.
- The Rust-seed rejection system spec now wraps its shell calls with
  `process_run_timeout` through `app.io.mod`; the focused contract check
  completed in 7.6s with `2 examples, 0 failures` instead of hanging on a
  child process.
- The `gui_entry_engine2d.spl` entry dropped the duplicate full-frame
  allocation/blit render path (`rt_u32_alloc_filled` +
  `rt_fb_blit_array32`) and now presents the same scene through the existing
  direct framebuffer writer only. The entry shrank from 505 to 392 lines.
- A follow-up reduced-source native-build probe after that trim still timed
  out at the 120s worker cap with no parser/import/semantic diagnostics:
  `build/os/simpleos_wm_simple_web_check_direct_fb_probe.err` contains
  `native-build worker timed out after 120s before producing a binary`. The
  live blocker remains compiler cost for this freestanding entry, not the
  removed duplicate framebuffer path.
- The entry now uses a local QEMU BGA setup (`rt_port_outw` + fixed
  `0xFD000000`) instead of importing the generic PCI-scanning
  `bga_init_framebuffer` module. This matches the QMP wrapper's `pmemsave`
  address and removes boot/memory framebuffer types from the entry closure.
- A comparable reduced-source native-build probe after the local-BGA change
  still timed out at the 120s worker cap with no parser/import/semantic
  diagnostics:
  `build/os/simpleos_wm_simple_web_check_local_bga_probe.err` contains
  `native-build worker timed out after 120s before producing a binary`.
- The entry is now self-contained: it replaced the remaining `os.*` imports
  (`serial_init`/`serial_writeln`, `mmio_write32`, and
  `simple_web_qemu_panel`) with local extern-backed helpers and the same tiny
  QEMU panel math. The wm-simple-web target source roots are now only
  `build/os/generated` and `examples/09_embedded/simple_os/arch/x86_64`.
- A self-contained reduced-source native-build probe with those roots still
  timed out at the 120s worker cap with no parser/import/semantic diagnostics:
  `build/os/simpleos_wm_simple_web_check_selfcontained_probe.err` contains
  `native-build worker timed out after 120s before producing a binary`.
- A comparison native-build of the existing minimal x86_64 GUI entry using
  only the examples source root completed before the cap and reported a
  semantic failure (`method has not found on type nil`), which confirms the
  worker can return diagnostics for small freestanding entries on this host.
  The remaining wm-simple-web blocker is therefore specific to this scene's
  compiler/native-build cost, not broad source-root discovery.
- The scene was reduced to the QMP-required framebuffer evidence only: initial
  and input-repaint colors in the fixed source region (`320..470 x 140..240`)
  and target region (`120..300 x 60..190`), plus the existing serial markers
  and fullscreen cover phase. The PS/2 setup helper chain was also replaced by
  a minimal `_poll_qemu_mouse_input` hook that consumes one pending controller
  byte before repainting.
- The entry is now 249 lines. Bounded probes for both
  `build/os/generated`+examples and examples-only source roots still timed out
  at the 120s worker cap with no parser/import/semantic diagnostics:
  `build/os/simpleos_wm_simple_web_check_minimal_input_probe.err` and
  `build/os/simpleos_wm_simple_web_check_examples_only_probe.err` both report
  `native-build worker timed out after 120s before producing a binary`.
- Because the entry has no imports, the wm-simple-web target source roots are
  now just `examples/09_embedded/simple_os/arch/x86_64`.
- Direct worker tracing showed the native-build timeout is dominated before
  this entry reaches native codegen. The worker reports
  `[native-build] Entry closure files: 1`, then runs interpreted because JIT
  compilation of the compiler/CLI path falls back. The original JIT blocker was
  a W1003 shared-mutable optional in
  `src/compiler/70.backend/backend/interpreter.spl` (`main_fn_opt`); that code
  now registers globals first, then scans for `main` without reassigning an
  optional `HirFunction`.
- After the W1003 fix, a fresh direct-worker trace no longer reports that
  specific error, but Cranelift JIT still rejects 58 compiler functions and
  falls back to the interpreter before native-build work begins. The remaining
  QMP build timeout is therefore a native-build worker/JIT coverage problem,
  not remaining source-root or scene-size bloat.
- `src/app/cli/native_build_main.spl` now launches
  `src/app/cli/native_build_worker.spl` with `--mode=interpreter`, avoiding the
  host-JIT attempt when native-build starts the worker. A focused source-entry
  help smoke passed, and the SimpleOS binary-contract spec now asserts this
  launcher contract. A bounded 85s patched-source launcher probe no longer
  reports `[INFO] JIT compilation failed` or `CODEGEN BODY`; it still times out
  before producing a binary because the interpreted worker loads the compiler
  and LLVM import graph. The wm-simple-web target keeps the larger 870s worker
  timeout for the live QMP path.
- The native-build worker now imports
  `app.io._CliCompile.compile_targets.{cli_native_build}` directly instead of
  the broad `app.io.cli_compile` facade, and both split compile modules no
  longer self-import that facade. The launcher also exports
  `SIMPLE_EXECUTION_MODE=interpret` around the worker process and restores the
  previous value afterward, because the forwarded `--mode=interpreter` argument
  alone does not reliably suppress the source-run JIT attempt. A focused
  `--list-optimizations` smoke passed through the patched launcher without the
  previous `[INFO] JIT compilation failed` line. A verbose 85s build probe now
  reaches real native-build phase markers (`Entry`, `Source dirs`, and
  `Entry closure files: 1`) before timing out, so the current blocker has moved
  past host-JIT startup and into the actual native-build/codegen duration.
- A single longer verbose probe with `--timeout 180` reached the same
  `Entry closure files: 1` phase and still timed out before producing a binary.
  Do not repeat short timeout probes; the next useful step is reducing or
  accelerating the actual native codegen path for the one-file entry, or running
  the live path with its configured 870s timeout on a host where that budget is
  acceptable.
- The wm-simple-web QEMU target now requests `--opt-level=none` instead of the
  generic aggressive native-build profile, because this lane only needs a
  one-file framebuffer/QMP evidence binary. The updated qemu runner unit case
  passed inside the otherwise-stale `qemu_runner_spec` run, but a direct verbose
  native-build probe with `--opt-level=none --timeout 210` still timed out after
  `Entry closure files: 1`. The timeout is therefore in native codegen/linking
  for the freestanding entry, not MIR optimization level alone.
- Follow-up found one concrete linker gap in that phase: the LLVM native linker
  only diverted RISC-V SimpleOS outputs to a freestanding linker, so
  `x86_64-unknown-none` could still fall through to the hosted C-runtime link
  path. Added an x86_64 SimpleOS branch that links the user object with the
  existing `crt0.s`, `baremetal_stubs.c`, `type_stubs.c`, `auto_stubs.c`, and
  `linker.ld` assets. The focused SimpleOS contract now asserts this wiring.
  A direct `--emit-object` trace probe still timed out before useful phase
  output, and `bin/simple check` on `llvm_native_link.spl` exited 255 after
  loader warnings without a diagnostic, so live native-build evidence remains
  open.
- The pure Simple native-build parser now consumes `--cpu` and
  `--linker-script`, exports `SIMPLE_NATIVE_BUILD_LINKER_SCRIPT`, and the
  x86_64 freestanding linker uses that script with the existing x86_64 linker
  script as fallback. This keeps the QEMU runner's emitted
  `--linker-script <path>` argument truthful instead of relying only on the
  hardcoded fallback.
- The default wm-simple-web QMP build now selects LLVM for
  `build/os/simpleos_wm_simple_web_check_32.elf`, so the live evidence lane
  exercises the x86_64 SimpleOS LLVM linker instead of falling through the
  generic x86_64 Cranelift default. The environment override still wins for
  explicit Cranelift diagnostics.
