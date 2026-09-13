# Compiled checker asm-volatile indented-block gap

- Status: CLOSED (2026-09-13) — not reproducible on
  `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`
  (50,093,192 B, 2026-09-06 09:59). See Re-check below.
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
## Re-check 2026-09-13 (BUGFIX-11)

`src/lib/nogc_async_mut_noalloc/baremetal/riscv/cmo.spl` no longer contains
`asm volatile` at all (rewritten to plain `extern fn` + `unsafe(capabilities:
[ffi])` calls), so the original repro file cannot be re-run as described.
The indented `asm volatile:` block grammar this doc names is otherwise still
live in the tree (`src/lib/nogc_async_mut_noalloc/baremetal/{arm,riscv}/startup.spl`,
51 files repo-wide use `asm volatile`). `bin/simple test
test/01_unit/baremetal/riscv32_startup_spec.spl --no-cache --no-cover-check`
(which parses `riscv/startup.spl`, containing multiple indented `asm
volatile:` blocks) -> `54 examples, 0 failures`, `PASS`, no `expected string
literal in asm block` error. Closing as not-reproducible: the exact
reported file/line no longer exists in that shape, and the grammar it
exercised parses cleanly today on the deployed binary. If the "compiled
checker" referenced here is a distinct Stage 4 tool with its own parser
path (not `bin/simple test`), re-open with that tool's own repro command.
