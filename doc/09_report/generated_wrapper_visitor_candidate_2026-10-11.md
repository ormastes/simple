# Generated wrapper visitor candidate

The fold generator skipped every struct field named `kind`, including fields
of wrappers that have no carrier dispatch. HIR comprehension iterators and
filters, thrown effect types, dimension-expression recursion, and frontend
comprehension clauses consequently disappeared from fold traversal.

`_fold_struct_body` now skips `kind` only for dialect carriers, whose existing
match already handles it. The five affected checked-in wrapper functions now
delegate to their existing kind walkers. Registry declarations and the registry
hash are unchanged. The callback visitor generator already applies the correct
carrier guard and needs no change.
The fifth bridge validates AST assembly constraint kinds, which contain no
callback-bearing children but must still reach their explicit variant match.

The focused `fold_wrapper_kind_spec.spl` checks emitted wrapper bridges and
carrier dispatch, then executes real HIR/frontend comprehension trees and an
effect containing a nested type. Initial context 40 must become 46, 46 and 42.
Dimension expressions contain no callback carrier, so their bridge is checked
in the emitted source rather than by an uninformative unchanged fold count.

Execution status: UNRUN. No admitted generator/test runtime is available.
The five generated output lines were updated manually to match the corrected
generator; canonical regeneration and a zero-diff freshness check remain
required before qualification. No bootstrap or production proof is claimed.
