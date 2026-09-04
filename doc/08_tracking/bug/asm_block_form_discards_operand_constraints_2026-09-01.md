# Block-form `asm:` silently discards its operand constraints

- **Filed:** 2026-09-01
- **Status:** OPEN
- **Found while fixing:** `rv64_wm_inline_asm_blocks_arch_mixed_and_operands_unsubstituted_2026-09-01.md`

## Symptom

Block-form inline asm can never bind an operand, on any backend. The operands
are written, accepted by the parser without a diagnostic, and thrown away.

```simple
asm volatile:
    "csrr {0}, mcause"
    out(reg) mcause          # <- parsed, then discarded
```

```simple
asm volatile:
    "invlpg [{addr}]"
    in(reg) vaddr            # <- parsed, then discarded
```

Real sites: `src/lib/nogc_async_mut_noalloc/baremetal/riscv/startup.spl`
(`:283`, `:319-320`, `:337`, `:358`), the `riscv32` twin, and
`src/os/kernel/arch/x86_32/paging.spl:362`.

## Mechanism

`Parser::parse_asm` (`src/compiler_rust/parser/src/stmt_parsing/asm.rs`) builds
the block-form `InlineAsmStmt` with `constraints: vec![]`. The operand
statements sit inside the parsed `Block`, but `extract_asm_block_strings` only
matches `Node::Expression(Expr::String(..))` and `Expr::FString{..}` — every
other statement falls through its `_ => {}` arm and vanishes.

The PARENTHESIZED form does this correctly: `parse_asm_parenthesized` collects
them via `try_parse_asm_constraint` into `constraints`, which
`mir/lower/lowering_stmt.rs` turns into a real LLVM constraint string, an
operand index for `rewrite_asm_placeholders`, and input/output vregs.

## Consequence today

Since 2026-09-01 the block form preserves its `{name}` braces (that was the fix
for the sibling bug), so `rewrite_asm_placeholders` finds no operand to bind and
leaves the placeholder literal, and the C sidecar replaces the line with
`# skipped Simple asm with unresolved operands`. So these instructions are
**no-ops** on the Cranelift/C-sidecar path.

This is not a new regression: before that fix the same lines were flattened to
bare tokens (`csrr 0, mcause`, `invlpg [addr]`) and the assembler rejected them
outright — the block never worked either way. Failing loudly at the emitter
would be better than a silent no-op, but the real fix is to bind them.

## Fix direction

Give the block form the same constraint collection the parenthesized form has,
so `out(reg) x` / `in(reg) x` inside an `asm:` block reach
`InlineAsmStmt.constraints`. Then the existing MIR lowering binds them with no
further change. Do NOT work around it by rewriting the `.spl` asm blocks.
