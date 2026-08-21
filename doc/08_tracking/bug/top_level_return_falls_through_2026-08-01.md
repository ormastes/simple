# A statement-level `return` does not terminate the function (compiled lanes)

- **Date:** 2026-08-01
- **Status:** **FIXED in the Rust seed** by `3487c07ce41` (verified RED -> GREEN
- **Verification 2026-08-21 (bug-status-consistency audit): PARTIAL, not fully fixed.** the seed half is real (3487c07ce41; `start_unreachable_block` at `lowering_core.rs:1515`, 3 call sites), but the mirrored pure-Simple `src/compiler/50.mir/` site is still OPEN. `bug_db.sdn` row is `fix-implemented-verification-pending`.
  on real native ELF binaries). The mirrored **pure-Simple** site in
  `src/compiler/50.mir/` is still **OPEN**. See "Fix landed" below.
- **Severity:** critical (silently changes control flow and return values)
- **Engines affected:** the **compiled** lanes (JIT and native codegen), in both
  the Rust seed and the pure-Simple compiler. The **tree-walking interpreter is
  CORRECT.**
- **Base:** `63c362526c2b01c5bc63697ab80aea1501ae65fe`

> **Correction to an earlier revision of this file.** It stated that the
> interpreter was also affected and that "no spec can catch it". That was a
> mislabelled lane: a bare `simple_seed foo.spl` selects the **JIT**, not the
> interpreter. Run through the interpreter (`simple_seed test`) the same
> assertions **pass 7/7** — see `test/01_unit/compiler/return_terminates_spec.spl`,
> added with this entry. Always name the lane you measured.

## Fix landed (Rust seed) — `3487c07ce41`

Root cause is as located below. The fix adds `start_unreachable_block()` to
`src/compiler_rust/compiler/src/mir/lower/lowering_core.rs` and calls it after
the terminator write in **all three** of `HirStmt::Return`, `HirStmt::Break`
and `HirStmt::Continue` in `lowering_stmt.rs`. The new block is unreachable by
construction, so it costs nothing when no statements follow.

### The defect has three members, not one

`break` and `continue` write their `Jump` terminator the same way and were
equally broken. `continue` is the **most severe of the three**, because the
dead statements mutate a live variable that is read after the loop:

```
fn cont() -> i64:
    var n = 0
    for v in [1,2,3]:
        continue
        n = n + 100
    n
```

Pre-fix this returned **300**; post-fix it returns **0**.

### Verification (PROVED, native lane)

Two release compilers built from the same tree differing only by this change;
fixtures compiled to real stripped PIE ELFs with `compile --native` and run:

| case | pre-fix | post-fix |
|---|---|---|
| two returns in a block | **3** | **1** |
| dead code after `return` | ran | silent |
| dead code after `break` | ran | silent |
| dead code after `continue` | **300** | **0** |

No-regression controls, byte-identical pre and post: early return out of an
`if`, early return out of a `for`, nested `if`-in-`if` return, guarded
fallthrough returns.

### The spec here is non-gating — PROVED, not inferred

`test/01_unit/compiler/return_terminates_spec.spl` passes **7/7 on the
interpreter using the OLD, UNFIXED seed**. This file already said the
interpreter is correct; measuring it confirms the consequence: **the spec
cannot fail on the lane `simple test` runs**, so it is a statement of the
contract, not a detector of this defect. `break`/`continue` cases were
deliberately NOT added to it for that reason — they would be equally vacuous.
The real gate is the native lane above. Anything that wants to catch a
regression here must compile and run, not `simple test`.

## Symptom

A `return` written at the **top level of a function body** (i.e. not nested
inside an `if`/loop/match arm) does not return. Execution falls through into the
statements after it, and for a value-returning function the result becomes the
value of the **last** `return` executed, not the first.

## Reproduction

`ret3.spl`:

```
fn a():
    return
    print "A-DEAD"

fn b() -> i64:
    return 1
    print "B-DEAD"
    return 2

fn c():
    print "c-live"
    return
    print "C-DEAD"

fn d(x: i64):
    if x > 0:
        return
    print "D-after-if"

fn main() -> i64:
    a()
    print "b={b()}"
    c()
    d(1)
    print "done"
    return 0
```

Seed **JIT** — this is what a bare `simple_seed <file>.spl` selects, NOT the
interpreter:

```
A-DEAD
B-DEAD
b=2
c-live
C-DEAD
done
```

Expected: no `*-DEAD` line, and `b=1`.

Seed native codegen — same verdict. Lane proved by disassembly
(`nm ret2.out | grep -c rt_enum_check_discriminant` = 1, a symbol emitted only
by `src/compiler_rust/**`):

```
before
DEAD-CODE-RAN
after
```

## Characterisation

| Shape | Behaviour |
|---|---|
| bare `return` as first top-level statement | **falls through** |
| bare `return` after other top-level statements | **falls through** |
| `return <value>` at top level, more code after | **falls through**; function returns the LAST return's value |
| `return` nested inside an `if` | correct — terminates |

So the defect is specific to a `return` at the **statement level of the function
body**. Nested-block returns are fine, which is why the codebase mostly works.

## Impact found in-tree

`src/compiler/70.backend/backend/llvm_ir_builder.spl` `emit_tbaa_hierarchy()`
used a top-level `return` to keep TBAA metadata switched off. The guard never
took effect, so **every** `.ll` the pure-Simple LLVM lane emitted carried TBAA
metadata — and that metadata was itself malformed (see the companion bug
`llvm_lane_emits_invalid_ir_2026-08-01.md`), making `llc` reject every module.

That site is now fixed, but it was **not** the only thing blocking the lane: a
six-line hello-world still fails there on a corrupt `target triple` and lost
constants (defects 2 and 3 of the companion entry, both still OPEN). Fixing this
one site is necessary, not sufficient.

The general risk is much wider: any `.spl` function that early-returns
unconditionally at statement level and has code after it is running that code.

### Family sweep over `src/compiler/**` (independent, 2026-08-01)

A scan for "a `return` statement whose next non-blank non-comment line has the
same indentation" over every `.spl` under `src/compiler/` returned 9 hits. Seven
are false positives — docstring prose whose line happens to begin with the word
"return". The two real sites are:

| Site | Intent of the guard | What actually happens |
|---|---|---|
| `70.backend/backend/llvm_ir_builder.spl:545` | keep TBAA emission off | TBAA emitted on every module, malformed — FIXED here |
| `30.types/type_system/effect_pass.spl:27` | "Skip effect inference in bootstrap (method calls crash in native binary)" | **the effect pass runs anyway** |

`run_effect_pass` returns `(modules, empty_warnings)` at statement level and then
continues into the full fixed-point effect inference. The guard has never taken
effect, so the comment's stated hazard is being run on every build.

`effect_pass.spl:27` is **deliberately left unchanged** here. Current stage2 is
green (`728 compiled, 0 failed`) *with the pass running*, so making the guard
work would change behaviour that nothing currently tests — that is a separate
change needing its own verification, not a drive-by. It is recorded so the
sibling is not lost.

## Root cause (located)

**MIR lowering writes the `Return` terminator into the *current* block but never
starts a new block.** Following statements keep emitting into that same block,
and a later `return` **overwrites** the terminator — so the last return wins and
the intervening statements still execute. A `return` inside an `if` lands in its
own then-block, so it behaves correctly.

HIR is innocent in both trees: it emits a Return node and keeps the following
statements, which is correct.

### Rust seed

- `src/compiler_rust/compiler/src/mir/lower/lowering_stmt.rs:857-896` —
  `HirStmt::Return` sets `block.terminator = Terminator::Return(ret_reg)` and
  returns. No new block, no `terminated` flag.
- `src/compiler_rust/compiler/src/mir/lower/lowering_core.rs:1536-1558` — the
  function-body loop walks every statement unconditionally, then patches the
  terminator only if it is still `Unreachable`.

The interpreter is correct and shows where the contract is honoured:
`interpreter/block_exec.rs:119-165` and `:210-300` early-return on
`Control::Return(_)`, and `interpreter_call/core/function_exec.rs:596,626` takes
the `Control::Return(v)` arm before the implicit-tail arm.

### Pure-Simple compiler (the `.spl`-side fix)

- `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:1138-1168` —
  `lower_return_expr` calls `br.terminate_return(...)` then returns a unit temp;
  no new block.
- `src/compiler/50.mir/mir_data.spl:526-557` — `set_terminator` is an
  unconditional overwrite. Note `current_block_has_explicit_terminator()` already
  exists at `:559-567` but **is not consulted** here.
- `src/compiler/50.mir/_MirLowering/function_lowering.spl:651-680` —
  `lower_block_expected` walks every statement with no terminated check.
- `src/compiler/20.hir/hir_lowering/statements.spl:400-412` and `:567-576` wrap
  Return as `HirStmtKind.Expr(HirExprKind.Return(...))`; that Expr-wrapping is
  why MIR handles it in the *expression* dispatcher and loses statement-level
  termination.

### Fix shape

After emitting the Return terminator, switch the builder to a fresh (dead) block,
or set a `terminated` flag that makes `set_terminator` and the block-statement
loop no-op until a new block starts. Sites: `lowering_stmt.rs:895` and
`expr_dispatch.spl:1159/1163`.

**Not attempted in this change.** It is a deep change to block termination that
needs its own stage2 build plus a full suite run to clear; the baseline to hold
is `728 compiled, 0 failed`. `return_terminates_spec.spl` is the executable
contract for whoever takes it.

## Do not

Do not "fix" call sites by wrapping the `return` in `if true:`. The guard has to
work, or the dead code has to be deleted.
