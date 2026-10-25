# Canonical enum finalizer duplicate-map undercharge

Source review demonstrated an independent baseline accounting defect in
`canonical_enum_builtin_finalizer_v1.spl`: duplicate detection used `Dict.has`
and assignment for every site while charging a fixed amount per site.
For 256 distinct colliding keys, the pure dictionary's two linear scans require
65,280 probes, already above the available fixed reservation 57,424 before
growth and text-key work. Later charges cannot prepay already executed work.

The repair removes that dictionary and formatted keys. Before examining any
prior site it reserves checked `4 * (index + 1)` logical work on the same actual
compilation account. It then compares only integer `(block, instruction)` pairs
against the prior prefix. No growing duplicate state, hash table or key bytes
remain. Exhaustion/overflow refuses before the scan; duplicate semantics stay
unchanged. Owner validation still precedes duplicate checking.

Focused authored specs cover one-short refusal with unchanged failed-reserve
ledger, sufficient-budget distinct coordinates, duplicate rejection and bound
overflow. All executable tests are UNRUN pending a qualified runtime. This
logical-work repair establishes no physical allocation bound or SOURCE receipt.
