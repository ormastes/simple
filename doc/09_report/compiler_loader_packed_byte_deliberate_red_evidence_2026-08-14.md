# Compiler loader packed-byte deliberate-red evidence

Date: 2026-08-14
Baseline: `0943ce963f05107046937456f8570b957aa939e5`

This receipt covers only the Rust-interpreter PBL-01 and PBL-02 semantic
negative-test contract. It is not Stage 4 or deployed-CLI evidence. Each
mutation changed one expected-value oracle, the canonical focused command
failed at the named assertion, and the oracle was restored without changing
production behavior.

## PBL-01 packed concat oracle

- Temporary mutation:
  `packed_byte_concat_preserves_storage` expected `Ok(4105)` instead of the
  production expectation `Ok(4104)`.
- Command:
  `cd src/compiler_rust && cargo test -p simple-compiler --test packed_byte_interpreter_semantics`
- Exit status: `101`.
- Named result: `packed_byte_concat_preserves_storage ... FAILED`; the
  assertion reported `left: Ok(4104)` and `right: Ok(4105)`.
- Suite summary: `3 passed; 1 failed`.
- Reversion: the expected value is again `Ok(4104)` and the test file has no
  diff from the baseline.

The failure proves that the final concat test observes the joined packed-byte
value and rejects an incorrect result. The already-retained green result in
the canonical plan remains the final-behavior evidence; it was not rerun in
this receipt session.

## PBL-02 projected-place write-back oracle

- Temporary mutation:
  `interpreter_byte_array_projected_place_mutators_write_back` expected exit
  code `1718` instead of the production expectation `1717`.
- Command:
  `cd src/compiler_rust && cargo test -p simple-driver --test interpreter_extern interpreter_byte_array_projected_place_mutators_write_back -- --test-threads=1`
- Exit status: `101`.
- Named result:
  `interpreter_byte_array_projected_place_mutators_write_back ... FAILED`; the
  assertion reported `left: 1717` and `right: 1718` with the projected-place
  rebuild/write-back message.
- Suite summary: `0 passed; 1 failed; 12 filtered out`.
- Reversion: the expected value is again `1717` and the test file has no diff
  from the baseline.

The failure proves that the focused test observes the removed byte, rebuilt
projected value, retained length, and first byte encoded by exit code `1717`.
The already-retained green result in the canonical plan remains the
final-behavior evidence; it was not rerun in this receipt session.

## Result

`PBL-01 deliberate-red: PASS`

`PBL-02 deliberate-red: PASS`
