# Worker memory reservation admission

Audience: TestRunner maintainers. Run
`test/01_unit/lib/test_runner/worker_memory_admission_spec.spl` and inspect all
four executed scenario verdicts.

1. Charge descendants to their owning root and retain smaller/missing roots'
   reservation floors.
2. Two maximum-i64 reservations must reject the snapshot instead of producing
   an aggregate that overflows the caller's accounting.
3. One maximum-i64 reservation remains valid and admits only into an empty
   matching budget.
4. Invalid charges reject admission; missing children retain reservations until
   the scheduler reaps them; exact-fit and one-unit-short boundaries differ.

The baseline failed the overflow scenario; the repaired Phase 1 interpreter
passed 4/4 after adding the descendant scenario.
This proves pure accounting only. RSS observations are admission evidence, not
hard OS enforcement. See
[evidence](../../../../08_tracking/bug/runner_memory_aggregate_overflow_2026_10_28.md).
