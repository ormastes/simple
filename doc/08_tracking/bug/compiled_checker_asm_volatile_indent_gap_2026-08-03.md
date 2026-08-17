# Compiled checker asm-volatile indented-block gap

- Status: **fix implemented; admitted compiled-checker verification pending**
- Severity: P1 (Stage 4 inventory blocker)
- Found by: `stage4_expr_batch`
- Owner: inline-assembly primary parser (unclaimed)

After the expression batch fixed the `unsafe:` diagnostic in frozen row
`source-000201`, the rebuilt compiled checker progressed to line 57 of
`src/lib/nogc_async_mut_noalloc/baremetal/riscv/cmo.spl` and reported
`expected string literal in asm block` for the canonical `asm volatile:`
indented form. This is a later independent grammar root; it is not evidence
that the unsafe-block fix failed.

The pure-Simple owner now routes the colon-indented form through the same
operand model used by parenthesized asm. It retains instruction strings,
`in`/`out`/`inout`/`lateout` operands, named operands, and option/clobber
directives. Unknown directives still diagnose and recover at the next line.

`test/01_unit/compiler/parser/asm_volatile_indented_block_spec.spl` covers the
exact historical RISC-V form, adjacent named operands/options, malformed-to-
valid recovery, and braced/parenthesized neighbors. Diagnostic execution
passes 4/4. Final closure still requires the retained historical source to be
replayed by a provenance-admitted compiled checker.
