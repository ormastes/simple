# `return` does not terminate its block: dead code after a `return` still executes and a later `return` overwrites the value

> **This file duplicates an earlier, canonical entry.** The same defect was
> already diagnosed in
> [`top_level_return_falls_through_2026-08-01.md`](top_level_return_falls_through_2026-08-01.md),
> which is what `test/01_unit/compiler/return_terminates_spec.spl` references.
> **Read that one first** — status, the landed fix, the `break`/`continue`
> family and the spec-vacuity finding are all recorded there. This entry is
> kept only for the native-lane evidence table below.

- **Date:** 2026-08-01
- **Area:** MIR lowering of `HirStmt::Return` / `lower_return_expr`
  - Rust seed: `src/compiler_rust/compiler/src/mir/lower/lowering_stmt.rs:857-896`
  - pure-Simple: `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:1138-1168`
    (`lower_return_expr`), terminator write in
    `src/compiler/50.mir/mir_data.spl:548-557` (`set_terminator`)
- **Severity:** medium-high. Confined to statements after a terminator in
  the SAME block (unreachable code), but that dead code EXECUTES and can
  mutate live variables — see the `continue` case below, which returned
  300 instead of 0. All *reachable* control flow was measured correct.
- **Status:** FIXED in the Rust seed (verified RED->GREEN on real native
  ELF binaries, see "Verification" below). The pure-Simple site is still
  OPEN — it could not be exercised because the deployed `bin/simple`
  rejects a bare `.spl` path.

## Symptom

Both lowerers write the `Return` terminator into the **current** block and
never open a new block afterward. Statements that textually follow a
`return` in the same block are therefore lowered into that same block and
still run, and a later `return` in that region **overwrites** the
terminator already stored there — last-return-wins.

`set_terminator` (mir_data.spl) unconditionally replaces the stored
terminator; `lower_block_expected`
(`src/compiler/50.mir/_MirLowering/function_lowering.spl:669-680`) walks
every statement with no check for an already-terminated block.

## Reproduction (PROVED)

Fixture:

```
fn a() -> i64:
    return 1
    print "A_TAIL_RAN"

fn c() -> i64:
    return 1
    print "C1"
    print "C2"
    return 3

fn d() -> i64:
    if true:
        return 1
        print "D_NESTED_RAN"
    5
```

Native lane — a real stripped PIE ELF, not an interpreter:

```
bin/simple_seed compile probe.spl --native -o probe_nat
./probe_nat
```

Observed (identical on the native ELF, the JIT `.spl` lane and the `.smf`
lane):

```
A_TAIL_RAN        <- unreachable statement executed
a=1
C1                <- unreachable statements executed
C2
c=3               <- WRONG, must be 1 (last-return-wins)
D_NESTED_RAN      <- unreachable statement executed inside a nested block
d=1
```

Expected: no `A_TAIL_RAN` / `C1` / `C2` / `D_NESTED_RAN` output, and
`c=1`.

## Not affected (measured, all correct)

Reachable control flow is fine — `Control::Return` propagation out of
nested blocks and loops works, and the ~20 existing
`current_block_has_explicit_terminator()` guards at control-flow joins do
their job:

```
fn e(x: i64) -> i64:
    if x > 0:
        return 1
    print "E_AFTER_IF_RAN"
    return 2
```

`e(5)` yields 1 and `E_AFTER_IF_RAN` is correctly NOT printed. An early
`return` inside a `for` body correctly aborts the loop. Nested
`if`-in-`if` returns are correct.

`src/compiler_rust/compiler/src/interpreter/block_exec.rs:134-146` is
**correct** — it breaks out of the statement loop immediately on
`Control::Return`. The tree-walking interpreter is not the defect; the
reproduction above goes through MIR on every lane tested.

## The same defect has three members, not one

`break` (lowering_stmt.rs:1328) and `continue` (:1345) write their `Jump`
terminator the same way and likewise never open a new block. The
`continue` case is the worst of the three because the dead statements
mutate a live variable that is read after the loop:

```
fn cont() -> i64:
    var n = 0
    for v in [1,2,3]:
        continue
        print "CONT_DEAD_RAN"
        n = n + 100
    n
```

Pre-fix this printed `CONT_DEAD_RAN` three times and returned **300**;
post-fix it prints nothing and returns **0**.

## Verification (PROVED, RED -> GREEN)

Both compilers were built by this lane from the same source tree
(`cargo build --release --bin simple`), differing only by the fix, and
both fixtures were compiled to real native ELF binaries and run:

| case | pre-fix | post-fix | expected |
|---|---|---|---|
| `a()` | `A_TAIL_RAN` printed, a=1 | silent, a=1 | silent, 1 |
| `b()` | `B_MID_RAN` printed, b=1 | silent, b=1 | silent, 1 |
| `c()` | `C1`,`C2` printed, **c=3** | silent, **c=1** | silent, 1 |
| `d()` | `D_NESTED_RAN` printed, d=1 | silent, d=1 | silent, 1 |
| `brk()` | `BRK_DEAD_RAN` printed | silent | silent |
| `cont()` | `CONT_DEAD_RAN` x3, **cont=300** | silent, **cont=0** | silent, 0 |

No-regression controls (reachable control flow), byte-identical output
pre- and post-fix: early return out of an `if` (`e(5)=1`, no
`E_AFTER_IF_RAN`), early return out of a `for` (`F_LOOP_BODY 1` only,
`f=2`), nested `if`-in-`if` return (`g(5)=1`), and
`guarded(5)=1 / guarded(-5)=2 / loop_ret=2`.

## Fix shape

After emitting a `Return` / `Jump` terminator, start a fresh (unreachable)
block so later statements lower into it instead of clobbering. Implemented
as `start_unreachable_block()` in `lowering_core.rs`, called from all three
of `HirStmt::Return`, `HirStmt::Break` and `HirStmt::Continue`. The new
block is unreachable by construction (nothing jumps to it), so it costs
nothing when the following statements are absent.
Note `current_block_has_explicit_terminator()` is **already used** at ~20
control-flow-join sites — it is not a dormant unused helper — so the new
guard must be added at the `Return` emission site itself.

## Corrections to earlier triage

Recorded so the next lane does not re-derive from a bad map:

- `current_block_has_explicit_terminator()` is **not** unused. It has ~20
  live callers across `50.mir/`.
- `mir_data.spl` is at `src/compiler/50.mir/mir_data.spl`, not under
  `_MirLoweringExpr/`.

### RETRACTED — a correction of my own that was wrong

An earlier revision of this file claimed there was **no** spec at
`test/01_unit/compiler/return_terminates_spec.spl` and that `edbea20a41c`
was "an unrelated LLVM TBAA change". **Both claims were false.** The spec
exists (98 lines, added by that very commit), and `edbea20a41c` is TBAA
work **plus** return-termination work — it also landed
`top_level_return_falls_through_2026-08-01.md`.

Two mistakes produced this, both worth avoiding:

1. I checked the **filesystem** (`find`) instead of **git**. This clone is
   sparse-checked-out, so the file is absent from disk while present in
   the tree — the known "git diff LIES when the index is sparse" trap.
   Existence questions must be answered with `git cat-file -e <rev>:<path>`.
2. I judged the commit by its **subject line** alone instead of reading its
   diffstat. The subject named only the TBAA half.
- The bug is **not** a reachable-code miscompile. Every reachable-return
  case measured correct; only the dead region after a `return` is wrong.

## Verification lane for the fix

```
cd <scratch>
bin/simple_seed compile probe.spl --native -o probe_nat && ./probe_nat
```

A fixed compiler must print neither `A_TAIL_RAN`, `C1`, `C2` nor
`D_NESTED_RAN`, and must report `c=1`.

Note `bin/simple` (the deployed pure-Simple binary) currently rejects a
bare `.spl` path with `error: unknown command`, so the pure-Simple lane
could not be exercised directly; the pure-Simple fix needs a working
self-hosted binary before it can be proved.
