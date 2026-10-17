# Hindley–Milner core native owner and range failures

Status: source candidate; native acceptance UNRUN; bug database admission pending.

The retained Phase 3 run using producer `0cd6d7c598f20af768774d68bc434f6a0b6660f6194a2e34e7eff48946e1aa9b`
reported 44 fatal diagnostics in `compiler.types.type_infer.core`. These include
ambiguous bare enum patterns, missing runtime enum identity, and native range
iteration represented as `I64` rather than an array. Source baseline:
`99b871a431ac7ff63e40a53aa6e9065facb954bf`.

The candidate imports the actual terminal `HirType` and `HirTypeKind` owners,
binds the three resolved types explicitly, and qualifies 57 pattern heads as
`HirTypeKind`. Result error patterns and all unification branch bodies remain
unchanged. Three dimension constraint loops use increasing integer cursors and
the same upper bound, operand order, and span as their original range loops.
Each cursor has a distinct name. No inference rule, mismatch guard, error,
substitution, or dimension constraint is removed or replaced with success.

This is a source workaround for the native producer's owner/range limitations;
it does not establish that all 44 diagnostics are resolved. The original
inference tests and a native control must establish successful substitution,
occurs rejection, mismatch rejection, and tensor/layer constraint emission.
The broad compiler/library/MCP/LSP and Phase 3 gates remain UNRUN.

Recovery: remove the explicit owner import/type annotations and qualified
pattern prefixes and restore the three original range loops from the baseline.
An external inverse-byte proof records the complete original file, rather than
checking only selected statements. No build or retry has been consumed here.
