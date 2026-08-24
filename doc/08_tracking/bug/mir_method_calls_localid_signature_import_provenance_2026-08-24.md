# MIR method-call lowering omits explicit `LocalId` signature provenance

**Date:** 2026-08-24
**Status:** SOURCE FIXED / BOOTSTRAP RECEIPT PENDING
**Owner:** Codex must-check bootstrap lane

## Reproducer

`sh scripts/check/check-signature-type-import-provenance.shs` reports one
offender across 1,816 files:

`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl (LocalId)`

The file uses `LocalId` in method signatures and constructors. Its declaring
module is `compiler.mir.mir_types`, but the existing explicit selective import
names only `mir_type_probe_text`; unrelated glob imports are deliberately not
accepted as surface-provenance evidence.

## Fix and acceptance

Add `LocalId` to the existing selective `compiler.mir.mir_types` import. Do not
change lowering behavior. Close this record only when the production checker
reports zero offenders. Its existing automatic and hand-authored fixture suites
are the adjacent regressions: missing imports must fail, valid selective imports
must pass, exclusions remain scoped, and ambiguity remains reported.

## Evidence

After the import-only fix:

- production scan: `PASS — 1816 file(s) checked, 0 offender(s)`;
- hand-authored self-test: 8/8 fixtures correct;
- automatic scanner self-test: 5/5 fixtures correct;
- direct environment-access working-tree audit: PASS;
- patch hygiene: PASS.

The exact-main checkout has no admitted `bin/simple`, so Simple lint and the
optimizer were not run and no Rust seed was substituted. The
`signature-type-import-provenance` must-check row remains TODO until a canonical
bootstrap invocation retains this checker output against an admitted Stage 4.
