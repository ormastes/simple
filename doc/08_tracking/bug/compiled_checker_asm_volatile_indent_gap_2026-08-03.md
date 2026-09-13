# Compiled checker asm-volatile indented-block gap

- Status: **open, rerouted**
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

## Triage 2026-09-13 (BUGFIX-7 lane)

Attempted repro: `bin/simple check src/lib/nogc_async_mut_noalloc/baremetal/riscv/cmo.spl`
-> `ERROR: no admitted cached self-hosted check worker artifact is available`
(the "compiled checker" this record refers to needs a self-hosted deploy this
host doesn't have). Also confirmed `src/compiler/10.frontend/core/parser.spl`
(this shard's listed file) has no `asm`/`asm volatile` parsing logic at all --
the record's own text ("compare the Rust parser's asm volatile grammar")
points at `src/compiler_rust`, not this pure-Simple file. Out of lane. No
change made.
