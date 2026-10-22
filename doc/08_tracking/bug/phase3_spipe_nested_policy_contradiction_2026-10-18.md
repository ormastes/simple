# Phase 3 SPipe nested test policy contradiction (2026-10-18)

The Phase 3 policy marked `.spipe/spipe` as `required-no-tests`, but parent
`ac32965e203be1d4be6b7993a026bfbc4cc3f5d9` pins SPipe
`0a00354eeea87ab7a74ef6e1aa3b8d5756bc1b75`, which has five tracked Simple specs.
Canonical nested discovery correctly rejects this with
`no-tests-policy-contradicted: .spipe/spipe`, preventing a whole-inventory run.

Remove the obsolete policy row. The unchanged default discovery path then
emits all five specs as `nested/simple-spec/execute` rows and records the exact
pinned/actual commit. No skip or new exemption is introduced; unrelated nested
modules and the fail-closed no-tests guard remain unchanged.

Regression: `test/01_unit/scripts/bootstrap_phase3_nested_inventory_test.shs`
uses the actual policy against a populated `.spipe/spipe` fixture and checks
that the obsolete classification still fails. An additional external proof
materializes the exact SPipe pin from the existing local object database,
checks the original policy refusal, and checks the corrected five-row inventory.
These checks validate inventory selection only; they do not run compiler tests
or establish whole Phase 3 success.
