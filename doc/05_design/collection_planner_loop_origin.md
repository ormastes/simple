# Canonical array loop analysis increment — 2026-10-03

This additive REQ-007 slice recognizes only a block containing a fresh empty
array local, one unlabelled `for` whose sole statement appends one typed value
to that local through an admitted Append symbol, and the final local value.
It produces Source -> Map with explicit loop provenance, never a fabricated
map symbol or callback. Mapping expressions initially admit only the induction
variable and typed scalar literals; other bindings and expression forms fail
closed. This is deliberately partial loop support, not complete equivalence.

Append identity, array receiver, argument count and order-preserving metadata
must match. Source, accumulator, loop and mapped expressions must be typed.
Source cannot refer to the fresh accumulator or induction binding. Extra
statements, labels, control transfer, nested loops, unknown calls, accumulator
reads/escapes and mismatched element types are rejected.

`CollectionPlanNode.loop_origin` defaults to nil, preserving existing call
constructors. Non-source nodes require exactly one of a resolved operation
symbol or loop origin. Loop origin stores the whole original block and loop HIR, induction symbol,
mapped expression, accumulator symbol and resolved append symbol. Source nodes
cannot carry it. Validator checks the retained typed operands and identities;
loop facts remain unknown and all rewrite proofs false.

The module collector attempts this recognizer at block frames. On success it
visits only the source and mapping expression once; it does not rescan the
append receiver or synthesize lambda captures. Unsupported blocks continue
ordinary traversal. Tests precede source and cover acceptance, rejection,
origin validation and one-region traversal. No runtime verification is claimed.
