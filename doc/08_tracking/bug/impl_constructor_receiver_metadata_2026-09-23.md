# Impl constructor-name receiver metadata

Status: OPEN / TEST_BLOCKED. Shared parser candidate accepted by independent
source review; parser execution and new compiler qualification are blocked by
disk capacity. No production GPU provider implementation is changed.

## Evidence and root

Fresh admitted Stage 2 compiler SHA-256
`98cbcdb15be2d04223bc03dd6ace3982b9e7826fbca9ec76e83a096f7a437cf3`,
source `e52ef0cc249d2e49b4d9d66070edd37ce269b4cc`, failed the Phase 2 full CLI
build in the three canonical `src/lib/nogc_sync_mut/gpu/engine2d/` owners
`sffi_cuda.spl`, `sffi_intel.spl`, and `sffi_rocm.spl`. Each `init` body failed
with `GlobalLoad: unresolved identifier 'self'`. Strict no-stub policy correctly
rejected these objects; this is not a CUDA/Intel/ROCm native ABI failure.

Exact retained log:
`/Users/ormastes/simple-tmp/macos-phase2-receiver-admission-20260923/build/evidence/phase2-receiver-stage2-capacity-retry/logs/compiler_cli_build.log`
(first errors at lines 46-51; failed files at lines 73-75).

`parser/src/types_def/trait_impl_parsing.rs` inferred static methods from the
names `init`, `new`, `create`, `default`, and `from_*`, even when the method had
an explicit receiver or used `self` in its body. The receiver admission fix in
PR #1380 made HIR trust parser metadata, exposing this remaining impl-parser
misclassification. Imported declarations must contain the receiver before ABI
arity is recorded; repairing it later in HIR would recreate the arity defect.

## Scoped correction

Only infer a static factory when it has no leading explicit receiver and its
body does not use `self`. Explicit `static` declarations remain authoritative;
mutable methods remain instances; the existing single receiver injection is
unchanged. Receiver-free factories retain their existing ABI.

This reuses the existing receiver walker. It does not expand that walker's
coverage of expression/node forms. In particular, self used only inside forms
the walker does not visit remains a separate limitation; no general parser
parity or full-language receiver claim is made.

## Verification plan and limits

- Extended `parser/tests/implicit_receiver_metadata.rs`: all five factory-name
  patterns, inherent and trait impls, explicit receivers without body use,
  receiver-free factories, and explicitly static declarations.
- Production-owner native fixtures: `cuda_ffi_init_receiver`,
  `intel_ffi_init_receiver`, and `rocm_init_receiver` under `test/fixtures/native/`.
  These exercise imported instance `init` with a nil dynamic library and assert
  fail-closed results, method dispatch, and static-factory mode. They do not
  establish GPU hardware availability or native driver operation.
- Baseline admitted compiler must reproduce the failure; a freshly built and
  separately qualified compiler containing this parser change must pass the
  same fixtures with `SIMPLE_NO_STUB_FALLBACK=1`. Never label the unchanged
  admitted compiler as containing this fix.
- Record compiler/source hashes, runtime capsule, commands, elapsed time, and
  process-tree RSS. Do not share writable caches between compiler lineages.
- Full Phase 2 CLI and runner remain separate admission gates, including the
  independent GUI failure already present in the retained baseline log.

No builds were launched during the matrix run or subsequent disk-capacity hold.

## Initial review and baseline reproduction

Independent Astra reviewer `/root/fix_phase2_intel_init` accepted the source and
parser-test design. This is a static review, not an execution PASS.

The ROCm fixture owner separately reproduced the sole `RocmFfi.init` unresolved
receiver failure with the admitted compiler: exit 1, 4.15 seconds elapsed,
113552 KiB sampled process-tree peak against a 976562 KiB enforced cap,
observer errors 0, quiescent 1. Preserved evidence:
`/Users/ormastes/simple-tmp/phase2-rocm-init-20260923/build/native_probe/rocm-init-receiver/stage2-98cbcdb15be2d042/`
(`red.log`, `red.env`, `red.time`). The original fixture used the `std` alias;
the central fixture imports the canonical owner explicitly. These are source
equivalent owner routes, but the central fixture still needs its own native
qualification. No green result is claimed.
