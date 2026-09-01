# riscv64 WM closure: `simple_asm_blocks.c` mixes x86 asm in and drops operand names

- **Filed:** 2026-09-01
- **Status:** OPEN
- **Blocks:** `scripts/check/check-simpleos-riscv64-wm-render-smoke-opensbi.shs`
- **Predecessors (all FIXED, do not re-file):**
  - `riscv64_wm_closure_unbuildable_asm_clobber_string_2026-09-01.md` — `clobber("memory")`
  - `deref_assign_after_multiline_call_parsed_as_multiply_2026-09-01.md` — parser + MIR deref lvalue
  - `Riscv64Context.fp_state`/`fp_pad` never declared (fixed in `fix(os/rv64): declare Riscv64Context.fp_state / fp_pad`)

## Where the gate stops now

With those fixed the whole Simple front end (parse -> HIR -> MIR -> codegen)
completes and the build reaches the ASSEMBLER. Verdict, verbatim:

```
ERROR — nothing was checked: WM kernel build failed: 18 errors generated.  build-riscv64-wm-kernel: ERROR — native-build failed for wm (rc=1), log: build/os/riscv64_wm/wm/kernel-build.log
```

(`rc=2`, captured directly into a variable, never through a pipe. The gate's own
30 selftest fixtures pass: `[rv64-wm] selftest OK (30 fixtures)`.)

## Two independent defects, both in `simple_asm_blocks.c`

That file is written by
`src/compiler_rust/compiler/src/pipeline/native_project/inline_asm_emit.rs:101`.

### 1. Every `asm` block in the closure is emitted regardless of target arch

The riscv64 build assembles x86 instructions:

```
in eax, dx          -> unrecognized instruction mnemonic, did you mean: li?
mov cr3, pd         -> unrecognized instruction mnemonic, did you mean: mv?
out dx, eax         -> unrecognized instruction mnemonic, did you mean: not?
mov out, cr3        -> unrecognized instruction mnemonic, did you mean: mv?
invlpg [addr]       -> unknown operand
```

The emitter has no arch predicate: blocks that are only reachable on x86_64 are
still emitted into the riscv64 translation unit and handed to the riscv64
assembler. 8 of the 18 errors are this.

### 2. Named operand placeholders are not substituted

```
mv out, tp          -> invalid operand for instruction   (`{out}` left literal)
mv tp, val          -> invalid operand for instruction
csrr 0, mepc        -> invalid operand for instruction   (rendered as `0`, not a register)
csrr 1, mtval
csrr 0, mcause
csrr 0, mhartid
csrc mip, msie      -> immediate must be an integer in the range [0, 31]
call 3              -> operand must be a bare symbol name   (x2)
```

Two shapes: a placeholder that survives verbatim as a bare identifier
(`out`, `val`), and one that is replaced by its OPERAND INDEX (`0`, `1`, `3`)
instead of by a register/symbol. Both make the emitted text unassemblable.
10 of the 18 errors are this.

## Not taken here

Out of scope for the riscv64 WM lane's reduced blocker, and defect 1 spans the
x86_64 asm blocks another lane owns. Recorded rather than worked around: no
`.spl` asm block was rewritten, and no gate fixture was weakened.

## Fix (2026-09-01)

Both defects fixed in one pass. Neither `.spl` asm block was rewritten and no
gate fixture was weakened.

### Defect 1 — `block_matches_target` was one-armed

`src/compiler_rust/compiler/src/pipeline/native_project/inline_asm_emit.rs`.
The target/arch notion was already at the emit site (the `target` triple), and
the filter already existed — it just had **only** the x86 arm, which rejected
RISC-V blocks from an x86 TU and did nothing in the other direction. It is now
symmetric: an explicit `AsmArch` classification (`X86` / `Riscv` / `Arm` /
`Neutral`) is derived from the target triple and from each instruction's
mnemonic, and a block is rejected only when it carries **unmistakable** evidence
of a family other than the target's. A line the emitter cannot attribute stays
`Neutral` and is kept for every target, so the filter can never silently drop a
block it merely failed to understand. No new arch parameter was added.

`mov` is classified x86 even though ARM shares it: the only two targets this
predicate can reject for are x86 and RISC-V, because `compile_inline_asm_c`
already bails out of the C sidecar entirely for aarch64/arm before reaching it.

### Defect 2 — the operand data is lost in the PARSER, not the emitter

Reported rather than hacked around, per the brief. The `{name}` marker is
destroyed at parse time by `Parser::extract_asm_block_strings`
(`src/compiler_rust/parser/src/stmt_parsing/asm.rs`), which rendered each
f-string part through `render_asm_placeholder` and pushed the **bare** token:
`"csrr {0}, mcause"` -> `csrr 0, mcause`, `"invlpg [{addr}]"` ->
`invlpg [addr]`, `"csrc mip, {msie}"` -> `csrc mip, msie`, `"call {3}"` ->
`call 3`. That is exactly the mistake the sibling `expect_string_value` already
documents and avoids for the PARENTHESIZED form ("Flattening to the bare name
emitted `csrr result, sstatus`"); the block form was never given the same
treatment, so the two forms disagreed on the same syntax.

The fix keeps `render_asm_placeholder` (so the 2026-08-17
`Identifier("stack_top")` Debug-format leak stays fixed and an unrenderable
expression is still a loud parse error) and **re-braces** its output. One
contract for both forms.

Downstream nothing else had to change: `rewrite_asm_placeholders` rewrites a
bound placeholder to `$N`, and either spelling (`$N` or a surviving `{name}`) is
already recognised by the emitter's `has_unresolved_simple_operand`, which
replaces the line with a skip comment instead of handing garbage to the
assembler.

### Still open, and deliberately NOT fixed here

**The block form declares operands that are thrown away.** In
`src/lib/nogc_async_mut_noalloc/baremetal/riscv/startup.spl` and
`src/os/kernel/arch/x86_32/paging.spl` the operand statements (`out(reg) mcause`,
`in(reg) vaddr`) sit inside the asm block, but `parse_asm` builds the block-form
`InlineAsmStmt` with `constraints: vec![]` — those statements fall through
`extract_asm_block_strings`'s `_ => {}` arm and vanish. So block-form asm can
never bind an operand, on ANY backend, and the placeholder lines above become
no-ops in the C sidecar rather than working instructions. Making the block form
carry its constraints is a separate parser feature, filed as
`doc/08_tracking/bug/asm_block_form_discards_operand_constraints_2026-09-01.md`. (This is not a new regression: those lines never worked —
they previously emitted unassemblable text.)

`clobbers: vec![]` in `parse_asm_parenthesized` is NOT part of this: parenthesized
clobbers travel in `constraints` and merge in `stmt_lowering.rs`.

### Evidence

- `cargo check --release --bin simple`: clean (0 errors).
- Reproduce tests, RED against this fix's own parent, GREEN after:
  - `parser`: `test_asm_block_form_keeps_operand_placeholder_braces`,
    `test_asm_block_and_paren_forms_agree_on_placeholder_spelling`
  - `compiler`: `native_inline_asm_riscv_target_rejects_x86_blocks`
    (non-vacuous: a real riscv block in the same run must still be emitted),
    `native_inline_asm_x86_target_still_rejects_riscv_blocks`,
    `native_inline_asm_riscv_skips_block_form_operand_placeholders`
- Full suites green: `simple-parser --lib asm` 31/31, `simple-compiler --lib
  inline_asm` 15/15.
