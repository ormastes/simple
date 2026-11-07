# Block-form `asm:` silently discards its operand constraints

- **Filed:** 2026-09-01
- **Status:** WAITING_VERIFY
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

The PARENTHESIZED form collects constraints via `try_parse_asm_constraint`.
The colon block form now collects operand constraints from its parsed
statements and passes them through the same MIR lowering, which builds the LLVM
constraint string, operand index for `rewrite_asm_placeholders`, and input/output
vregs.

## Consequence today

Before this fix, block-form operand statements were discarded. The C sidecar
then replaced unresolved placeholder lines with comments, silently turning
them into no-ops. A second loss point existed in Cranelift codegen: it
registered only the instruction strings from MIR and ignored inputs, outputs,
and register constraints. This also silently mishandled fixed-register forms
such as `rdmsr`, whose template has no placeholders to reveal the missing
bindings.

The parser now preserves block-form constraints. The Cranelift path now rejects
operand-bound or register-constrained asm before registry insertion, and the C
sidecar rejects any unresolved operands or constraint directives instead of
emitting comments. Raw asm with only the volatile memory clobber remains
supported. LLVM remains the backend that binds register operands.

## Fix direction

Give the block form the same constraint collection the parenthesized form has,
so `out(reg) x` / `in(reg) x` inside an `asm:` block reach
`InlineAsmStmt.constraints`. Do NOT work around it by rewriting the `.spl` asm
blocks.

## Fix implementation

- Block-form parsing collects operand and supported directive constraints and
  errors on unrecognized statements.
- Cranelift codegen rejects unsupported nonempty MIR inputs, outputs, and
  register constraints before registering a sidecar block.
- The sidecar emitter rejects unresolved placeholders and operand directives.
- Regression coverage includes the RISC-V output and x86 input block forms,
  sidecar rejection, and fixed-register `rdmsr` MIR matching
  `src/lib/nogc_async_mut_noalloc/baremetal/x86_64/msr.spl`.

Implementation is awaiting focused compiler verification and review.
