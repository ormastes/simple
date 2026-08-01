# `return` does not terminate its block: dead code after a `return` still executes and a later `return` overwrites the value

- **Date:** 2026-08-01
- **Area:** MIR lowering of `HirStmt::Return` / `lower_return_expr`
  - Rust seed: `src/compiler_rust/compiler/src/mir/lower/lowering_stmt.rs:857-896`
  - pure-Simple: `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:1138-1168`
    (`lower_return_expr`), terminator write in
    `src/compiler/50.mir/mir_data.spl:548-557` (`set_terminator`)
- **Severity:** medium. **Confined to statements after a `return` in the
  SAME block** — i.e. strictly unreachable code. All *reachable* return
  semantics were measured correct (see "Not affected" below).
- **Status:** OPEN — diagnosed and reproduced, not yet fixed.

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

## Fix shape

After emitting a `Return` terminator, start a fresh (unreachable) block so
later statements lower into it instead of clobbering, and/or make
`set_terminator` refuse to overwrite an existing explicit terminator.
Note `current_block_has_explicit_terminator()` is **already used** at ~20
control-flow-join sites — it is not a dormant unused helper — so the new
guard must be added at the `Return` emission site itself.

## Corrections to earlier triage

Recorded so the next lane does not re-derive from a bad map:

- `current_block_has_explicit_terminator()` is **not** unused. It has ~20
  live callers across `50.mir/`.
- There is **no** landed regression spec at
  `test/01_unit/compiler/return_terminates_spec.spl`, and commit
  `edbea20a41c` is an unrelated LLVM TBAA-metadata change.
- `mir_data.spl` is at `src/compiler/50.mir/mir_data.spl`, not under
  `_MirLoweringExpr/`.
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
