# riscv_dual_arch_spec.spl shadows 7 kernel types — real fields/methods never exercised

## Status (2026-08-10): converted to describe/it, real types wired in, now genuinely RED

The file (and its byte-identical `test/01_unit/os/` twin) has been rewritten
to import all 7 real kernel types and converted to `describe`/`it` sspec
format. All 7 types were swapped — none deferred, all were discoverable in
`dual_arch_contract.spl` / `fpga_orchestration.spl` / `backend_test_verify.spl`.

**Before the fix** the file had no `describe`/`it` blocks (a `print`-based
`main()`). It DID execute under `bin/simple test` (contrary to the original
uncertainty below) but the harness treated the whole file as **one** example
and failed it outright because zero `describe`/`it` examples were declared:

```
$ rm -rf .build/test_daemon_light
$ bin/simple test test/unit/os/riscv_dual_arch_spec.spl
...
error: test-runner: no examples executed
error: test-runner: spec executed nothing (zero-examples)
SPEC FILE VERDICT: test/unit/os/riscv_dual_arch_spec.spl declared>=1 executed=0 passed=0 failed=1 dropped=1 unrun=1 reason=zero-examples
Results: 1 total, 0 passed, 1 failed
```

Binary measured: `bin/release/x86_64-unknown-linux-gnu/simple` (the symlink
target of `bin/simple` at the time), mtime `2026-08-10 11:06:25`.

**After the fix**, with the shadow classes deleted and real imports
(`use os.kernel.arch.riscv_shared.dual_arch_contract.{ArchDescriptor,
DualArchContract, Rv32HardwareTree, QemuVirtContract}`,
`.fpga_orchestration.{FpgaOrchestration, LaneStatus}`,
`.backend_test_verify.{BackendTestEntry, VerificationStage, AcceptanceMatrix,
PromotionGate}`) driving 22 `it` examples across 8 `describe` blocks (one per
real type/file grouping — `FpgaOrchestration`+`LaneStatus` share
`fpga_orchestration.spl`, `BackendTestEntry`+`VerificationStage`+
`AcceptanceMatrix`+`PromotionGate` share `backend_test_verify.spl`), the spec
is genuinely **RED — left RED, not softened**, per `.claude/rules/testing.md`:

```
$ rm -rf .build/test_daemon_light
$ bin/simple test test/unit/os/riscv_dual_arch_spec.spl
spec failure: 22 of 22 example(s) failed (exit 1)
Results: 22 total, 0 passed, 22 failed
```

Root cause of the RED (a genuine, separate defect, not a spec-authoring bug):
every failure is `semantic: variable <field> not found`, e.g. `variable
'xlen' not found` inside `ArchDescriptor.is_rv32()`'s body (`return xlen ==
32`), `variable 'rv32_linux' not found` inside `DualArchContract.
both_linux_capable()`, etc. The real kernel-type methods in
`dual_arch_contract.spl` / `fpga_orchestration.spl` / `backend_test_verify.spl`
reference their own instance fields **without** a `self.`/`me.` prefix (bare
`xlen`, `rv32_linux`, `ram_mb`, `cpu_model`, `bitstream_ready`,
`compile_pass`, `shared_truth_ref`, `category`, `is_generated_only`,
`is_external_rtl`, `rv64_compile`, `rv32_compile`, ...) — a style that
apparently type-checks/compiles but is not resolved by the `bin/simple test`
execution path (tree-walk interpreter per `.claude/rules/testing.md`'s
run-vs-test divergence note). This was previously invisible because the spec
never called the real methods at all (see "What's wrong" below) — the shadow
classes' hand-rolled inline logic always used `d.field`/local-var reads, which
masked this gap entirely. **This is a new, separate, currently-open defect in
the field-resolution semantics of bare-name field access inside `me`/instance
methods under the test-runner's interpreter — filed here as evidence, not yet
independently tracked or root-caused further** (needs a `doc/08_tracking/bug/`
entry of its own if not already covered by
`reference_hir_elem_type_annotations_are_unreliable_use_local_mir_type_of.md`
or a related engine-divergence note; out of scope for this pass to fix, since
fixing it means changing compiler field-resolution behavior, not the spec).

Same 22/22 RED reproduced byte-identically on the `test/01_unit/os/` twin
(`Results: 22 total, 0 passed, 22 failed`); `diff` between the two files is
empty.

## Original filing (2026-08-10, pre-fix)

- **File**: `test/unit/os/riscv_dual_arch_spec.spl` (whole file, 239 lines)
- **Real product code**: `src/os/kernel/arch/riscv_shared/dual_arch_contract.spl`,
  `src/os/kernel/arch/riscv_shared/backend_test_verify.spl`,
  `src/os/kernel/arch/riscv_shared/fpga_orchestration.spl`
- **Found during**: bounded first pass on `spec_shadow_reimplementation_worklist.tsv`

## What's wrong

The file declares 7 local classes (`ArchDescriptor`, `DualArchContract`,
`Rv32HardwareTree`, `QemuVirtContract`, `FpgaOrchestration`,
`BackendTestEntry`, `VerificationStage`, plus 3 more not in the worklist:
`LaneStatus`, `AcceptanceMatrix`, `PromotionGate`) that share names with real
kernel types but are NOT structurally compatible with them:

- Real `ArchDescriptor` has 9 fields (`has_m_ext`, `has_a_ext` in addition to
  the spec's 7) plus business-logic methods `is_rv32()`, `is_rv64()`,
  `is_gc()`, `linux_capable()`, and static factories `rv32gc()`/`rv64gc()` —
  none of which the spec exercises.
- Real `DualArchContract` has 9 fields (`rv32_isa/abi/mmu`, `rv64_isa/abi/mmu`
  in addition to the spec's 3) plus `both_linux_capable()`/
  `any_linux_capable()`/`is_symmetric()` and static factories
  `gc_contract()`/`rv64_only()` — the spec constructs a 3-field version
  directly and hand-computes the "both"/"any" logic inline instead of calling
  the real methods.
- Real `Rv32HardwareTree` and `QemuVirtContract` similarly have extra
  required fields (`boot_rom_addr/size`; `dtb_path`, `append_args`,
  `device_count`) and real business methods (`is_linux_minimal()`,
  `has_console()`, `is_rv32()/is_rv64()/has_kernel()/has_dtb()`) that the
  spec reimplements inline as free functions instead of calling.

Additionally: this file has no `describe`/`it` blocks — it's a `print`-based
smoke script with its own `main()`. It is not clear it runs under
`bin/simple test` at all; it may be dead code entirely.

## Why not fixed in this pass

Fixing requires supplying the additional required constructor fields for all
7+ shadowed types, replacing the spec's hand-rolled boolean logic with calls
to the real methods (`is_gc()`, `linux_capable()`, `both_linux_capable()`,
etc.), and converting the file to the `describe`/`it` sspec format (or
confirming it's dead and should be deleted) — beyond a bounded import-swap
pass.

## Unblock condition

Rewrite against the real `dual_arch_contract.spl` / `backend_test_verify.spl`
/ `fpga_orchestration.spl` types, filling all required fields, calling the
real business-logic methods (not reimplementing them), and converting to
`describe`/`it` so it participates in the daemon-run corpus and CI verdict.
