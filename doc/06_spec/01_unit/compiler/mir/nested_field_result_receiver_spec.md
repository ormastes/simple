# MIR nested-field Result receiver recovery

**Status: authored manual; current-source execution and SPipe generation pending.**
Executable: `test/01_unit/compiler/mir/nested_field_result_receiver_spec.spl`.
Positive native fixture:
`test/fixtures/compiler_entrypoint/nested_field_result_receiver/main.spl`.
Negative compiler fixture:
`test/fixtures/compiler_entrypoint/nested_field_result_receiver_unknown/main.spl`.

1. Parse and lower the actual positive fixture through the repository frontend,
   HIR and MIR owners. Require no HIR or MIR errors for local, direct-field and nested
   field receivers. Each helper predicate must contain exactly one actual close
   call and one canonical Result discriminant comparison.
2. Check both predicate spellings on direct and nested field chains. `is_ok`
   compares the Ok discriminant zero; `is_err` compares Err discriminant one.
3. Parse a negative fixture with one valid `stream` field and an absent requested
   field. Require compiler errors, with no fabricated Result discriminant in
   the invalid function. An unrelated field's type must not be guessed.

The actual native positive fixture additionally checks both Ok/Err truth
outcomes, six total close effects and two close effects retained in each rooted
field. It prints its golden PASS line only after those semantic checks. The
unit MIR inspection cannot substitute for running that executable.

The repair queries declared metadata only. It does not evaluate or lower the
receiver during type lookup. Existing class/provider owner selection remains
unchanged; arbitrary generic-owner field substitution and cross-trait casts are
outside this fix. The unknown-field negative may fail compilation; it must never
be executed or admitted as a successful binary.

Run actual matching admitted compiler unit tests and the native fixture with
both required backends/producer cohorts, retaining source/producer/runtime
identities, exit codes and output. Then generate this manual and require zero
stubs. No parser-only test, expected.stdout file or old-producer failure can
establish current-source runtime PASS. The isolated old-producer diagnostic is
recorded separately in the bug report.
