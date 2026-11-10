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

## 2026-11-11 addendum — P3 traverse lane ne1 verdict: BLOCKED (stays WAITING_VERIFY)

Provenance verified at the `origin/release/1.0.0` tip: both fix commits are
ancestors of the refreshed 2026-11-11 seed's build commit `0791c2b7f4a7`:

- `82405d7bfccc` (2026-11-07, "fix: collect asm block constraints and reject
  unresolved operands") — block-form operand collection in
  `src/compiler_rust/parser/src/stmt_parsing/asm.rs` + C sidecar rejection in
  `native_project/inline_asm_emit.rs`.
- `23ede5e6b783` (2026-11-07, "fix: reject unbound MIR asm operands in
  Cranelift") — `E-ASM-OPERANDS-UNSUPPORTED` hard error in
  `src/compiler_rust/compiler/src/codegen/instr/mod.rs`.

So the deployed refreshed seed necessarily carries the fix; what remains is
runtime verification, which this lane could not complete:

- The focused parser/codegen regression tests
  (`codegen_instr_tests/inline_asm.rs`, asm-block parser tests — per the
  2026-11-07 luna lane note) require cargo/rustc, which is forbidden in this
  lane.
- Seed-level behavioral probes hang on this host: `bin/simple.exe
  native-build --backend=cranelift --entry <probe> -o <out> --no-cache` on a
  trivial block-form `asm volatile: "nop" / out(reg) x` program stayed
  CPU-bound mid-compile (log frozen, no output artifact, never reached the
  probe's codegen; no `E-ASM-OPERANDS-UNSUPPORTED` emitted) — the same
  silent-CPU-bound family as the stage4 worker, not asm-specific.

Exact grant commands: (1) `cd src/compiler_rust && cargo test inline_asm`
(parser + codegen rejection suites); (2) on a host where the seed compile
finishes: `bin/simple native-build --backend=cranelift --entry
<operand-probe.spl> -o <out>` must fail with `E-ASM-OPERANDS-UNSUPPORTED`,
and the volatile-only control (`asm volatile: "nop"` with no operands) must
still compile.

Status stays WAITING_VERIFY / open. Lane evidence:
`build/review/p3fix-ne1-20261111.sdn` row 7.
