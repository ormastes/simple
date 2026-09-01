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
