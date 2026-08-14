# Stage 3 HIR contract model partial integration

- Status: FIX IMPLEMENTED; native verification pending
- Date: 2026-08-14
- Owner: compiler HIR model/lowering

## Failure

A current-source pure-Simple Stage 3 build reached all 616 parsed sources and
failed closed in HIR lowering:

```text
[ERROR] phase 3 FAILED
unresolved name: HirContractClauseKind
unresolved name: HirContractOutcome
```

The diagnostic associated the poisoned module with
`src/std/nogc_sync_mut/io/sffi_common.spl`, but that module does not reference
either name.  The authoritative missing definitions were in
`src/compiler/20.hir/hir_definitions.spl`: verification MIR/backend consumers
had landed while the corresponding HIR contract types and `HirFunction` field
had not.

## Fix

Restore the typed `HirContractClauseKind`, `HirContractClause`,
`HirContractOutcome`, and `HirContractBlock` model; retain an optional
`HirFunction.verification_contract`; initialize it explicitly in both HIR
lowering constructors; preserve it through semantic resolution; and remove the
fragile positional `HirFunction` pattern used only to read `is_extern`.

## Evidence and unblock condition

- Failed build log: `build/native_probe/stage3-fresh/build.log` (exit 1).
- The first cache-preserving retry no longer reported the missing contract
  names and was observed externally terminated. Its retained log proves only
  that no compiler error or candidate was emitted; it does not retain the exit
  code or sampled RSS. This is not proof of a second compiler defect and not
  proof that the HIR fix passed end to end.
- Exact source check/regression and a fresh pure-Simple Stage 3 build must pass
  without these unresolved names.
- The produced Stage 3 must then pass the existing hello and module-qualified
  field-layout probes.  Rust-seed execution is not acceptance evidence.
