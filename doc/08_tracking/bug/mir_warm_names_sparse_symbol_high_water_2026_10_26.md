# MIR logical-name warming scans the symbol high-water range

Status: source repair candidate; executable regression, optimizer CLI and
paired p50/p95 time/RSS evidence UNRUN. The live frozen compiler is unchanged.

`driver_pipeline_lowering.spl` warms symbol owners with raw IDs from zero to
`next_symbol_id` for every module. Its density assumption is false:
`SymbolTable.register_preserved_symbol` accepts a pre-numbered ID, inserts one
dictionary row and advances the high-water mark to ID+1. Two stored rows can
therefore require a billion membership probes. Missing IDs contribute no
owners, so their iteration is redundant. This is source-level work amplification;
it is not a sampled attribution of the live warm_names stage's elapsed time or
stable RSS. No claim about actual live symbol cardinalities is made.

The repair snapshots actual scalar keys, filters exactly `0 <= id < high_water`,
and uses a private numeric-only bottom-up merge before warming. Ascending ID
visitation, duplicate owner-path warming, empty owner handling, module key/name
and flat bootstrap registry warming remain unchanged. No rich values snapshot,
new process cache, registration rewrite, scope change or SOURCE authority is
introduced. Scratch arrays now depend on actual stored keys (O(S) space and
O(S log S) sort), rather than high-water iteration O(H). This allocation tradeoff
requires paired measurement and does not imply an RSS reduction.

Cycle2 review correction: the initial candidate reused the HIR codec sorter,
whose nil discrimination formats every compared value. That would introduce
O(S log S) text allocations at scope0/paused. The corrected private sorter uses
only relational integer comparisons/indexed scalar writes and independent
buffers; shared codec nil semantics are untouched. Actual `Dict<i64,...>` keys
and the same `0 <= id < high_water` comparisons retain the old integer domain.
Integer3 is explicitly tested; no `== nil` check or text reinterpretation occurs.
Malformed non-integer/nil dictionary keys are not newly admitted as valid
symbols; runtime representation of such corrupt input is not qualified here.

The new focused executable spec uses actual SymbolTable registration, checks
two entries with high-water1000000001, exact ascending visitation versus the
old dense oracle on a bounded fixture, key3, empty/duplicate owners, negative
and out-of-range keys, unchanged dictionary size/high-water and canonical memo
results. Three scenarios remain authored UNRUN without a qualified general
self-hosted CLI. No seed fallback, heavy job or live process attachment.

The bounded target history/symbol check found the same high-water loop and no
equivalent sparse traversal repair. Independent Astra source review is required
before source-only landing. Performance acceptance stays OPEN until real
regressions and paired p50/p95 wall time plus peak/steady RSS meet the optimize
skill's budgets; no speedup or compiler/Phase3 qualification is claimed.
