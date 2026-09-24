# BorrowGraph: moving one field flags a read of a DIFFERENT field
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- **Spec (RED, intentionally left failing):** `test/01_unit/compiler/deep/borrow_check_move_1_spec.spl`
  — "moving one field does not flag a read of a DIFFERENT field" (`assert_false failed: got true`),
  file line ~65. Neighbour example "different dynamic index locals still conflict
  conservatively" passes, so projection granularity works for Index but not Field.
- **Component:** `src/compiler/55.borrow/borrow_check/borrow_graph.spl` (`pub class BorrowGraph`,
  `record_move` / `record_use` conflict test on `PlaceElem.Field` vs whole-local / other-field).
- **Observed (2026-09-15, seed `bin/release/aarch64-unknown-linux-gnu/simple`):** move of
  `x.field(0)` followed by a read of `x.field(1)` reports an error — the conflict test treats
  any two places sharing a base local with Field projections as conflicting, instead of
  requiring the same field index (or an overlap with a whole-local place).
- **Unblock condition:** conflict detection distinguishes `PlaceElem.Field(i)` from
  `PlaceElem.Field(j)` for i != j (per-field move granularity), while whole-local reads still
  conflict with any field move.
- **Context:** found during the 2026-09-15 full-suite failure sweep. The spec itself was also
  missing its `use compiler.borrow.borrow_check.*` import and its `field_of` helper; those were
  restored (spec now runs: 7/8 pass) — only this genuine behavior gap remains red.

