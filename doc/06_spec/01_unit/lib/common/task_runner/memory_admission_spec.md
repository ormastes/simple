# Common process memory admission

Audience: build/test runner maintainers. Run
`test/01_unit/lib/common/task_runner/memory_admission_spec.spl` with the qualified
runner and inspect all three executed scenario verdicts.

1. Preserve positive reservation floors and measured overshoot; reject invalid
   charge inputs.
2. Accept the maximum representable total and reject overflow or a prior error.
3. Admit exact fits; reject overcommit, nonpositive reservations and invalid
   budget/charge values.

All arguments in a call use one unit. This pure policy has no OS effects.
The focused Phase 1 interpreter receipt passed 3/3; native qualification and
mixed BuildRunner/TestRunner scheduling remain open. See
[evidence](../../../../../08_tracking/bug/runner_memory_aggregate_overflow_2026_10_28.md).
