# Compiled checker asm-volatile indented-block gap

- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- Severity: P1 (Stage 4 inventory blocker)
- Found by: `stage4_expr_batch`
- Owner: inline-assembly primary parser (unclaimed)

After the expression batch fixed the `unsafe:` diagnostic in frozen row
`source-000201`, the rebuilt compiled checker progressed to line 57 of
`src/lib/nogc_async_mut_noalloc/baremetal/riscv/cmo.spl` and reported
`expected string literal in asm block` for the canonical `asm volatile:`
indented form. This is a later independent grammar root; it is not evidence
that the unsafe-block fix failed.

Reproduce with the rebuilt checker against that exact file. The follow-up must
compare the Rust parser's `asm volatile:` grammar, preserve existing braced and
parenthesized asm behavior, and add exact, adjacent, malformed, and recovery
coverage before changing the asm owner.
