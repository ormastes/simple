# RV64 inline-assembly immediate becomes an AST debug string

**Claimed:** 2026-08-12, Codex `/root/rv64_inline_asm_immediate`

## Failure

The admitted compiler aborts an RV64 kernel rebuild after handing LLVM this
assembler text:

```text
li t1, Identifier("stack_size")
LLVM ERROR: Do not know how to promote this operator!
```

Evidence is retained at
`/mnt/data/.simple/qemu/artifacts/sosix-qemu/rebuild/rv64-real-exec-20260812T030500Z/riscv64/kernel-build.log`.

## Root cause

Legacy indented `asm volatile:` strings are parsed as ordinary interpolated
strings. The seed parser renders each interpolation expression with its AST
debug representation in `extract_asm_block_strings`; it also discards the
following operand declarations. The pure-Simple core parser preserves the
braces but likewise has no operand representation for that legacy block form.
LLVM therefore receives neither a literal immediate nor a bound asm operand.

## Required owner fix

The compiler must preserve and bind asm operands as typed constraints before
LLVM lowering. It must never send `Identifier(...)`, `Integer(...)`, or another
frontend AST debug representation to a target assembler. Coverage must include
the exact named immediate and an adjacent integer-immediate case. Rewriting the
RISC-V firmware string is not a compiler fix.

## Status

The pure-Simple LLVM template owner now binds the closed
`Identifier("<constraint-name>")` leak through the existing typed constraint
index and unwraps signed `Integer(<i64>)` literals. Focused verification is in
progress. Complex expression debug forms remain deliberately unsupported; the
legacy colon parser's discarded-constraint defect is a separate prerequisite
before this firmware can be considered successfully lowered end to end.
