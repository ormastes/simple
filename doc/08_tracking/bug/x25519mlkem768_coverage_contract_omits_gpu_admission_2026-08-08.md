# X25519MLKEM768 coverage contract omits GPU admission owners

## Status

Open

## Impact

The X25519MLKEM768 coverage contract can report a high branch percentage while
excluding the CUDA/Vulkan/Metal build-admission and measurement decision
owners. It therefore cannot prove the feature's near-100% branch-coverage
requirement or a security-critical GPU promotion gate.

## Evidence

- `src/app/test/x25519mlkem768_coverage_contract.spl` declares 23 owners but
  omits `gpu_build_admission.spl`, `gpu_measurement_qualification.spl`, and
  `gpu_lifecycle_snapshot.spl`.
- `test/fixtures/crypto/x25519mlkem768/critical_branch_symbolic_v1.psv`
  already declares those owners, plus `gpu_dispatch`, `evidence_contract`,
  `matrix_receipt`, and `executed_row_composer`.
- `test/01_unit/os/crypto/x25519mlkem768_gpu_build_admission_spec.spl`
  exercises the omitted fail-closed tuple branches but is absent from the
  coverage run spec list.

## Reproducer

Compare owner records from:

```text
src/app/test/x25519mlkem768_coverage_contract.spl
test/fixtures/crypto/x25519mlkem768/critical_branch_symbolic_v1.psv
```

The symbolic inventory contains coverage owners not present in the contract
denominator.

## Required fix

Reconcile the owner and spec manifests with the symbolic critical inventory;
replace hand-copied owner counts and synthetic coverage rows in the receipt
composer/unit/system fixtures with contract-driven data; then produce a fresh
instrumented native coverage receipt. Do not claim a promotion-grade coverage
percentage until that receipt includes every reconciled owner.

## Resume

Owner: X25519MLKEM768 acceleration lane.

Start with `src/app/test/x25519mlkem768_coverage_contract.spl`, then run the
focused coverage composer, critical-inventory, and manifest-existence specs on
the self-hosted binary. A fresh native coverage run is additionally required
before closing this record.
