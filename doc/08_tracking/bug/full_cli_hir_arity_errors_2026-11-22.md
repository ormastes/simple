# Full-CLI build: 7 HIR call-shape errors (2026-11-22)

**Where:** Stage 2 qualification task `compiler_cli_build` (entry
`src/app/cli/_CliMain/main_and_help.spl`, 4407-file closure), Stage 2 built from
release head `53795406ba6` (sha256 `0c056de6...`). HIR lowering rejected seven
call shapes; the bootstrap-CLI closure never reaches these files, so they only
surface on the full CLI.

Classification: **(a)** caller/callee mismatch in source; **(b)** the call is
right for the intended callee but the build bound a different module.

| # | File | Callee | Class | Status |
|---|------|--------|-------|--------|
| 1 | `src/lib/gc_async_mut/gpu/browser_engine/dom_accessors.spl` | `BeDomEvent.create` | a | fixed |
| 2 | `src/compiler/70.backend/backend/llvm_native_link_runtime_owner.spl` | `dir_remove` | a | fixed |
| 3 | `src/app/editor/gui_shell.spl` (+ `gui_shell_core.spl`) | `editor_layout_compute_rects` | a | fixed |
| 4 | `src/os/_QemuRunner/os_build_run.spl` | `verify_rv64_qemu_user_proof_contract` | **b** | fixed (not compile-checked) |
| 5 | `src/lib/nogc_sync_mut/orchestration/host_linux_service_current_v4.spl` | `linux_service_enrollment_verify_v1` | a | fixed |
| 6 | `src/compiler/50.mir/mir_data.spl`, `_MirLowering/module_lowering.spl` | `begin_function` | a | fixed |
| 7 | `src/app/devhub/cmd_bb.spl` | `print_info` | a | fixed |

## 1. `BeDomEvent.create` — 7 args to a 4-parameter constructor (a)

`dom.spl:520` is `create(event_type, namespace_uri, bubbles, cancelable)`. Three
empty-path fallbacks (`dom_accessors.spl` 1231, 1246, 1272) still passed the old
7-argument shape `(type, "", "", "", "", bubbles, cancelable)`; the six route
variants lower in the same file already use 4. This is the arity fix of PR #305,
restored once by `079bb487b4f` and re-reverted by the release transplant
(`88aac2ffe28` / `bb3f6ab8ab2`). Fix: drop the three surplus `""` — they were the
target id/tag strings, which `create` already initialises to `""`.

## 2. `dir_remove(staging)` — missing `recursive` (a)

Explicit import `std.nogc_sync_mut.io.dir_ops.{dir_remove}`, which is
`(path, recursive: bool)` (as are `io_runtime` and `app.io.dir_ops`). Both sites
run right after `file_delete(staged)`, the only file in the `secure_temp_dir`
staging directory, so the faithful value is `false` (plain rmdir of an empty
directory); `true` would widen it to a recursive delete. Call sites introduced by
`79261e409e9`.

## 3. `editor_layout_compute_rects` — missing `x, y` (a)

`src/lib/editor/view/layout.spl:109` is `(layout, x, y, w, h)`; `tui_shell.spl`
passes all five. `gui_shell.spl` 687/693 pass `(layout, initial_width,
initial_height)`. The GUI editor area starts at the origin, so the fix inserts
`0, 0`. `gui_shell_core.spl` 857/863 carry the identical defect (not reached by
this build) and are fixed the same way.

## 4. `verify_rv64_qemu_user_proof_contract(output)` — callee outside the snapshot roots (b), fixed (not compile-checked)

Two files answer the module path `hardware.riscv_common.core.riscv_formal`:

- `src/hardware/riscv_common/core/riscv_formal.spl:291` —
  `verify_rv64_qemu_user_proof_contract(output: text)`. The intended callee: it
  scans QEMU serial output, which is what `verify_qemu_formal_output` passes.
- `src/lib/hardware/riscv_common/core/riscv_formal.spl:142` — was
  `verify_rv64_qemu_user_proof_contract(code_start: i64, exit_code: i64)`
  (first seen in `9cbdb7774d4`, 2026-05-19), with zero callers anywhere in
  `src/` or `test/`.

**Cause — not resolver precedence** (an earlier revision of this section blamed
it). The native-build source snapshot freezes only
`src/{app,lib,compiler,os,plugins}`
(`src/app/io/_CliCompile/native_build_snapshot_roots.spl:27`; `src/os` and
`src/plugins` join an explicit cut as companion roots at `:64-71`).
`src/hardware` is not in the snapshot, so inside it the bare
`hardware.riscv_common.core.riscv_formal` has exactly one candidate, the
`src/lib` file. That is why the failing log lowers
`lib.hardware.riscv_common.core.riscv_formal` and never opens the
`src/hardware` file: the file is absent, not outranked. The precedence comment
at `src/compiler/80.driver/driver_entry_closure_core.spl:2224` is not
contradicted by this evidence.

**Owner direction:** `src/hardware` is not to become a snapshot root. The rv64
QEMU user-proof step runs only on a host provisioned with QEMU and must be an
explicit skip elsewhere; `src/os` must compile from the existing roots.

**Fix:**

- `src/lib/hardware/.../riscv_formal.spl`: the zero-caller 2-arg function is
  replaced by the 1-arg `(output: text)` marker check — same marker list and
  same `Err` text as the `src/hardware` one. The six `src/os` importers
  (`_QemuRunner/{os_build_run,runner_targets,scenario_catalog,scenario_disks,scenario_exec}.spl`,
  `qemu_runner_part2.spl`; only `os_build_run.spl:791` and
  `qemu_runner_part2.spl:674` call it) are unchanged and now type-check against
  the module they actually bind in the snapshot.
- Behaviour difference, stated: the `src/hardware` function additionally runs
  `verify_riscv_events` over three hard-coded retire events. That part does not
  read `output`, always succeeds for those constants, and stays covered by
  `test/01_unit/hardware/riscv_common/riscv_formal_contract_spec.spl`. The lib
  function therefore returns `Ok`/`Err` for exactly the same transcripts; only
  the `Ok` text differs (`verified 6 proof markers` vs
  `verified 3 formal events`). No caller reads the `Ok` text.
- `test/03_system/os/qemu/os/usermode/rv64_user_exec_qemu_spec.spl` (and its
  `test/system/` twin, kept byte-identical): the only consumer of
  `verify_qemu_formal_output`. Its existing `_can_run()` probe
  (`which <qemu_system>`, kernel image present) already printed `SKIP: ...`;
  it now also calls `std.spec` `skip(name, reason)`, so a host without QEMU
  prints `it RV64 user-mode QEMU proof ... skipped (<reason>)`. With QEMU and
  the kernel present the path is unchanged.

**Still open:**

- Five other module paths exist in both `src/hardware` and `src/lib/hardware`
  with differing contents (`fpga_linux.riscv_fpga_linux`,
  `riscv_common.core.riscv_external_formal`,
  `riscv_common.pkg.riscv_generated_core_pkg`,
  `riscv_common.pkg.riscv_linux_pkg`, `rv64gc.top.rv64_machine`). The same
  snapshot-only binding applies to any bare `hardware.*` import of them.
- `skip()` is a printed marker (`src/lib/nogc_sync_mut/spec/__init__.spl:46`);
  whether the runner tallies such an `it` as skipped rather than passed was not
  checked.

## 5. `linux_service_enrollment_verify_v1` — missing `agent_helper_template_bytes` (a)

`e11d1f2f9ed` (milestone_0021 PR2) added the seventh parameter and updated
`host_linux_service_install_v3.spl`, but not the installed-state re-verification
in `host_linux_service_current_v4.spl:575`. Fix: read it the same way as its
three siblings, `host_linux_service_read_v4(root_reader, "agent-helper-template.sdn")?`
— the leaf name `linux_service_enrollment_fixed_files_v1` installs and the loop
directly below re-compares.

## 6. `begin_function(..., None)` — `None` to non-optional `span: Span` (a)

`d5943d12405` rewrote `nil` to `None` at two synthetic-function call sites
(`mir_data.spl:2342`, `module_lowering.spl:1867`); the parameter is `span: Span`
and `MirFunction.span` is `Span`. Every other synthetic caller (module init,
trait thunks, trait conversion) passes `Span.empty()`, so these two now do too.
Effect on consumers: `core_codegen.spl:1087` yields debug line 1 for both a
missing span and `line == 0`; the loop-view capture now records an empty span
node for these two functions instead of none, as it already does for the other
synthetic functions. The comment at `core_codegen.spl:1084` still says `nil`.

## 7. `print_info(msg)` — devhub `print_info` is `(label, value)` (a)

`cmd_bb.spl` imports `print_info` from `app.devhub.output` (`label, value`),
every other devhub caller passes two arguments. Fix:
`print_info("PR #<n>", "not ready: <reason>")`. Visible change: the line now
reads `PR #12: not ready: ...` (one added colon, label bold when colour is on).

## Verification

Not compile-checked end to end. Two single-file `native-build` fixtures with the
admitted Stage 2 binary (4G cgroup) both hit their timeouts (400 s / 100 s)
before finishing; they produced only the resolution evidence in §4. The six
fixes were checked by reading each callee signature and its other callers. The
full-CLI closure was not rebuilt.
