# MIR loses the element type of unannotated collection receivers

Canonical id: `mir_unannotated_collection_element_type_lost_2026_10_20`
Status: OPEN (tagged source workaround active)
Found: phase-3 attempt 6 MIR clusters (`p3p7-20261020/mirfail/unresolved_method.txt`),
reproduced single-module on producer8 (release_phase3 `613fc7b54bc`).

## Symptom

`unresolved method call: pop` / `get` / `unwrap` on array receivers whose
element type MIR cannot name:

- `var pending = [from_action]; pending.pop()` — an unannotated array literal.
  `lower_array_lit` never remembers an `Array(T)` HIR type, and on the `--entry`
  path (no inference) the binder has none either. The `pop` arm
  (`lower_array_first_or_last`) refuses to decode without an element type, so it
  fails closed (correct: guessing would mis-decode `[text]`).
- `scope.caps.pop().unwrap()` with `scope: &Scope` — the field of a `&T`
  parameter has no declared element type at MIR (same class as the `&T` param
  field gap in p6 NOTES).
- `w = []; w.get(i)` with `list`-typed `sha1_process_block(h: list, ...)`
  (`src/lib/common/crypto/sha1.spl:124-127`, 8 errors).

Fixture: `C:/dev/simple-bootstrap-storage/fixer-p8meth/fixtures/q5.spl`
(6 errors on producer8 and on the p8meth producer).

## Workaround (active)

`src/compiler/80.driver/action_graph/coordinator.spl` annotates
`var pending: [text] = [from_action]` (`@workaround bug=mir_unannotated_collection_element_type_lost_2026_10_20`).
Verified with fixture q6 (annotated form builds and runs; `reach` returns the
right values).

Not worked around (left failing, recorded): `route_capability_scope.spl:91,108`
(`&T` field), `sha1.spl` (`list` alias).

## Fix direction

Remember `Array(T)` on the array-literal result when every element's HIR type
agrees (`lower_array_lit`), and resolve `&T` param field / `list` element types
from declarations. Remove the coordinator annotation after a producer with that
fix builds the original form.

Bug DB (`bug_db.sdn`) reconciliation pending: the qualified `simple check-dbs`
CLI is not available on this host; this dated record carries the fields.
