# Foreign-call borrow origin

Executable specification:
`test/01_unit/compiler/resource/foreign_call_borrow_origin_spec.spl`.
Bug: `resource_borrow_pinning_not_enforced_2026-08-07`.
Contract: resource declaration architecture, safety invariant 3.

**Execution status: pending.** This companion is an authored manual, not generated
runtime evidence. No case has been executed in this campaign. A source-compatible
self-hosted runner must execute the spec, and `spipe-docgen --no-index` must
replace/validate this companion with zero stubs before verification admission.

| Scenario | Operation | Required result |
|---|---|---|
| Declared foreign call | Parse/lower an extern and pass its actual callee operand to the NLL checker with a live loan | Origin Foreign; explicit missing non-retaining-contract escape diagnostic |
| Local compatibility | Parse/lower a same-spelled local function and check the same loan lifetime | Origin Source; no borrow errors in the legacy body |
| Summary isolation | Give a foreign call a same-name local read-short summary | Retention remains unproved and produces the escape diagnostic |
| Missing provider | Request the actual extern operand before provider metadata registration | Origin Unknown; a local summary cannot authorize it |
| Signature repair | Resolve a named extern and repair its return signature | Foreign origin and escape diagnostic are preserved |
| Scalar control | Pass a scalar value to a foreign call without creating a loan | No borrow errors |
| Alias retention | Copy the reference before passing it to the foreign target | Escape diagnostic follows the reference alias |
| Call terminator | Pass the loan through a terminating call edge | Same escape diagnostic as an instruction call |

The tests assert exact boundary diagnostics rather than accepting any nonempty
error list. The source-classification tests also assert successful HIR/MIR
lowering and presence of the actual emitted callee. Existing resource lifetime
and ordinary move/borrow specs are required compatibility evidence.
