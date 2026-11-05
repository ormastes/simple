# Negative integer match arms fail native MIR lowering

Status: OPEN. Observed 2026-09-30 with self-hosted Linux producer
`9088595d5a51191f9895293c8d6c8c17ddefe4d6e12dbf04015b705372b02308`.

A function matching an `i64` with `case -1`, `case -2`, and `case _` parses
and passes HIR, then fails MIR with
`B5b: match has multiple wildcard arms`. Expected: distinct negative integer
patterns and a final fallback arm. No runtime execution occurred.

Reproducer evidence: first compile log in
`/mnt/simple-bootstrap-6b2/cli-memory-route-fix-20260930/compile-attempt1.log`.
The original five negative arms are retained in the diagnostic source snapshot
`policy-attempt1.spl` beside it. The streaming route diagnostic uses explicit
comparisons pending a compiler fix; this does not change the route decision.

## Landed repair — 2026-11-05

PR #6840 (merged into release/1.0.0, commit a180469b01b). The flat bridge
already preserved `Unary(Neg, IntLit)` in pattern position; the missing link
was `hir_normalize_integer_pattern_literal`, which only folded integer casts.
It now folds `Unary(Neg, IntLit(n))` into `IntLit(-n)` with the operand type,
so MIR scalar match dispatch accepts negative integer arms. The i64 minimum
stays unfolded and fails at the ordinary unsupported-pattern diagnostic.
Non-literal negation and cast normalization unchanged.

Evidence: `test/01_unit/compiler/hir/negative_integer_match_pattern_spec.spl`
(5 scenarios) PASS under the Rust seed interpreter on an aarch64 Linux host;
manual at `doc/06_spec/01_unit/compiler/hir/negative_integer_match_pattern_spec.md`;
neighbor `suffixed_integer_pattern_spec.spl` 5/5 unchanged. End-to-end
native-build validation remains pending on an admitted self-hosted binary
(seed native-build is additionally gated by an unrelated
snapshot-index-drift admission error).
