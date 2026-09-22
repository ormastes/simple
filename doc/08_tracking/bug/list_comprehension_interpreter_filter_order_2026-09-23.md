# List comprehension interpreter evaluation order

Status: OPEN; separate from native HIR projection-loss fix and Phase2 optional-Add.

The native list-comprehension contract evaluates, per input element, its filter
and then its projection if accepted. This preserves source-order side effects
and does not evaluate rejected projections.

Current Rust interpreter `interpreter/expr/collections.rs`, ListComprehension
arm, calls `comprehension_iterate` first. That helper in
`interpreter_helpers/utilities.rs` evaluates all filters and collects accepted
environments; the caller then evaluates all projections. A filter or projection
that changes visible state observes a different order from a fused traversal.

Concrete source-level reproducer:
`test/fixtures/native/list_comprehension_semantics.spl`. Native contract stdout
is stored next to it as `.expected`: filter 1, filter 2, project 2, filter 3,
filter 4, project 4. The interpreter source predicts filters 1–4 followed by
projects 2 and 4. This ordering has been established by source inspection, not
claimed as a newly executed interpreter result.

Parent explicitly excluded interpreter expansion from the current native HIR
lane. Do not claim cross-engine side-effect parity until a dedicated fix and
interpreter red/green test establish it. Any future fix must preserve per-item
pattern scope, filter failure propagation, iterable evaluation count, and
rejected-projection non-evaluation without retaining one environment per item.
