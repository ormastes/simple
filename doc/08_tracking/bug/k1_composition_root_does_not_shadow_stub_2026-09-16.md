# K1 composition root does not shadow bootstrap_k1_selected stub — static K1 backend table is dormant

**Status:** OPEN (loader/composition redesign pending)

**Found:** 2026-09-16, during full-bootstrap verification of the K1 kernel-closure
receipt gate (`scripts/bootstrap/write-k1-composition-receipt.shs`) on lane
`fix/bootstrap-k1-receipt-seed-stage2` (PR #1028).

## Symptom

`src/compiler/driver/bootstrap_k1_selected.spl` ships in the repo as an
852-byte fail-closed stub: `install_selected_k1_backend_table_v1()` returns
`false` unconditionally. The real 2778-byte implementation is generated under
`build/.../compositions/kernel_llvm_cranelift/src/compiler/driver/bootstrap_k1_selected.spl`
and injected via `--source build/.../compositions/kernel_llvm_cranelift` on the
full-CLI entry (`src/app/full_cli/main.spl`).

A controlled transcript experiment (logs at
`/tmp/k1order6.MLK1Fa/first.bin.log`, replay harness
`/tmp/replay-transcript.py`) proved the composition root never shadows the stub
in **either** `--source` order: the in-tree `src/compiler/driver/...` path wins
resolution, so every stage2/stage3 binary built through the full-CLI entry
carries the stub, and `install_selected_k1_backend_table_v1()` returns `false`
at runtime.

The K1 static backend table is therefore dormant: no stage binary ever
installs the selected cranelift+llvm adapter set via this path.

## Cause

Composition-source shadowing of an in-tree logical path does not happen for
`bootstrap_k1_selected.spl` in the current source-resolution order. The
mechanism that was supposed to let the generated composition replace the stub
(putting the composition root earlier in `--source`, or later) does not apply
to this path in either arrangement.

## Consequence

1. The K1 composition receipt gate previously failed any real full bootstrap
   with `Stage3 kernel closure contains plugin source`, because the gate's
   blanket plugin ban contradicted the entry's real closure (150+ plugin
   refs, e.g. `src/plugins/backend_vhdl/_VhdlProcess/process_codegen.spl`
   reachable via `driver_aot_pipeline.spl`), and the composition module
   scanned at the logical stub path with the stub's 852 bytes.
2. The gate now records the honest state instead of rejecting it: every
   `src/plugins/*` / `src/compiler/*` closure path is classified against
   `doc/04_architecture/compiler/plugin_arch/kernel_closure.sdn`
   (K0/K1 admitted, P-static counted), and the composition binding is recorded
   as `stageN_k1_binding=stub-fallback` when the scanned logical path has the
   stub's content length (852) rather than the composition's (2778).

## Fix direction (not done here)

The loader/composition resolution needs a redesign so the generated
composition root deterministically shadows the in-tree stub for the K1
selected-module path (or the stub needs to be produced by a pre-pass that the
gate can verify). Until then, receipts carry `stub-fallback` and the runtime
`install_selected_k1_backend_table_v1()` keeps returning `false`.
