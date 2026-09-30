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
