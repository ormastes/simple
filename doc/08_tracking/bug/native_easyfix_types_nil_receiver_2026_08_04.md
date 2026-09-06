# Native EasyFix types nil receiver

## Status

Open behavioral bug; HIR compilation is repaired, native execution is not.

## Symptom

`stage4_easy_fix_types_contract.spl` compiled and linked two modules without
stub fallback, but execution reported `runtime error: field access on nil
receiver` and terminated with exit 132 before the expected exit-30 sentinel.

## Evidence

- Build log: `build/focused/stage4-easy-fix-types/native-build.log`
- Execution log: `build/focused/stage4-easy-fix-types/exec.log`
- Binary SHA-256: `0bc4f93d41e6c57a18b072c2acda33f7d67281f2f1798c0a56de8d9620b046e5`

## Boundary

Do not weaken the contract or claim an EasyFix behavioral PASS. Diagnose the
first failing constructor/field access with a smaller native fixture in a
separate bounded lane; this does not justify a runtime alias or feature-local
nil workaround.
