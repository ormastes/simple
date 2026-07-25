# Match-binding silent-wrong-value bug — investigation report

## Bug report as given

"On the NATIVE `--entry` build path, a genuine binding arm `case x:` in a
`match` over an i64 scrutinee can bind the WRONG VALUE (silent-wrong)."
Suspected location: `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`
and/or `expr_dispatch.spl` `lower_match_case` (the default-binding-value
plumbing that maps a `Binding` pattern's symbol onto the scrutinee's MIR
local).

## Actual root cause (NOT where suspected)

The `lower_match_case` / `emit_if_chain_dispatch` / `emit_switch_dispatch`
binding-to-scrutinee plumbing in `switch_operators_calls.spl` and
`expr_dispatch.spl` is **correct**. Traced with instrumentation: the
`Binding` pattern's symbol is aliased to the exact same `LocalId` as the
scrutinee (`self.local_map[default_symbol.id] = scrut_local`), and every
downstream `NamedVar`/`Var` lookup for the bound name resolves to that same
local. This part of the pipeline was not the source of the bug.

The real defect is in the **MIR optimization pass**
`src/compiler/60.mir_opt/mir_opt/var_reassign_ssa.spl`, specifically
`ssa_alloca_apply_def_store` (used by `ssa_alloca_transform_blocks`, which
`_MirToLlvm/core_codegen.spl::llvm_bootstrap_ssa_function` runs on every
function before LLVM-IR emission):

```
val written = var_reassign_written_local(inst)
if written.?:                      # <-- BUG: Option<i64>::Some(0) is falsy
    val written_id = written.unwrap()
    ...
```

`written` is `i64?` (`Option<i64>`). The seed/bootstrap interpreter's `.?`
truthiness check on a boxed `i64?` collapses `Some(0)` to false (a
C-style "is the payload nonzero" shortcut instead of a tag check). So
whenever the MIR local being **defined** by an instruction has id `0`,
`ssa_alloca_apply_def_store` silently treats it as "nothing written" —
no rename, and critically **no `Store` is emitted** into that local's
alloca slot. Any later **read** of that same local (a completely separate
code path, `ssa_alloca_rewrite_operand`, which uses a plain `i64`
`local_count_index` scan, unaffected by the `.?` bug) correctly detects the
local is slotted and inserts a `Load` from the never-initialized alloca —
producing raw uninitialized stack memory as the "value".

### Why this hits `case x:` bindings specifically, and why it looked like a match/binding bug

MIR local id `0` is not a rare corner case — it is the **first local id any
Unit-returning function's real body ever uses**, because typed-return
functions (`fn f() -> i64:`) always allocate a synthetic `Return`-kind
placeholder local at id `0` first, pushing every real user local to id
`>= 1`. A **Unit-returning function** (`fn f():`, e.g. the extremely common
`fn main():`) has no such placeholder, so its first real temp/var reliably
lands on id `0`. Any local landing on id 0 that also needs "slotting" (via
`ssa_reassigned_locals_for_blocks` — multi-def — or
`ssa_cross_block_live_locals` — cross-block-live) permanently loses its
value. Because `match n: case 1: ...; case x: print(x)` was being tested
inside `fn main():` (no explicit return type, matching a very natural way
to write the reported repro), the scrutinee/binding's backing local
happened to land on id 0, making the bug look specific to
match-binding plumbing. It is not — it is a general MIR-opt correctness bug
that affects **any** locally-reassigned or cross-block-live variable whose
MIR id is 0, independent of match/binding syntax.

(There is a second, narrower issue also observed: `ssa_cross_block_live_locals`
over-eagerly flagged a local as "cross-block-live" inside a genuinely
single-block function in one of the repro cases. That heuristic bug is what
*triggered* slotting for a trivial `val abc = 5; print(abc)` body, but it is
orthogonal to the correctness defect: once a local **is** slotted for any
reason — including a legitimate loop reassignment — the missing-Store-on-id-0
bug silently corrupts it. Fixing the `written.?` collapse is the minimal,
correctness-restoring fix; the over-eager single-block flagging is a
separate efficiency/precision concern, not touched here per "never
over-engineer.")

## Fix

`src/compiler/60.mir_opt/mir_opt/var_reassign_ssa.spl` —
`ssa_alloca_apply_def_store`: replaced the `if written.?: ... else: ...`
truthiness dispatch with an explicit `match written: case Some(written_id):
... case nil: ...` on the Option's variant tag, which does not collapse
`Some(0)`. See `scratchpad/match_binding.patch` (34-line diff, comment +
logic only, no behavior change for any non-zero written id).

This is the same bug **class** already flagged once in this file's own
docstring (the negated `if not written.?:` form was previously found to
mis-evaluate on struct-boxed optionals and was replaced by the "positive"
`if written.?:` form) — that fix addressed the general case but missed the
`Some(0)` collapse specifically, because `0` is a valid, common `LocalId`.

## Shape-characterization matrix (oracle vs native, BEFORE fix)

| # | Shape | Oracle | Native (before fix) | Verdict |
|---|-------|--------|----------------------|---------|
| 1a | `fn main(): match n: case 1: print(100); case x: print(x)`, n=1 | `100` | `140722992981656` (garbage stack addr) | **silent-wrong** |
| 1b | same, n=7 | `7` | `140721474050408` (garbage) | **silent-wrong** |
| 1c | same shape but wildcard `case _: print(999)` instead of binding, n=1 | (n/a, wildcard always non-binding) | `999` instead of `100` | **silent-wrong** (proves bug is NOT binding-specific — plain wildcard default in the same `fn main():` shape also misroutes/reads garbage) |
| 2 | `fn main() -> i64: ... case x: print(x * 2)` (n=9) | `18` | `18` (once `-> i64` used) | correct — confirms bug tied to Unit-return `main`, not to arithmetic-on-binding |
| 3 | binding arm listed BEFORE the literal arm (`case x: ...; case 1: ...`) | `9` | `9` | correct (once fixed / with typed return) |
| 4a | match on a local | `9`/`100` | matches | correct |
| 4b | match on a fn parameter | `9` | `9` | correct |
| 4c | match on a call result (`match get_val(): ...`) | `9` | `9` | correct |
| — | plain `fn main(): val abc=5; print(abc)` (no match at all) | `5` | `0` | **silent-wrong** (root-cause isolation case — no match/binding involved at all) |
| — | `fn helper(): val abc=5; print(abc)` called from typed `main()` | `5` | `0` | **silent-wrong** (confirms it's about the DEFINING function's return type / local-id-0, not about `main` specifically) |
| — | `fn main() -> i64: val abc=5; print(abc); return 0` | `5` | `5` | correct (typed return avoids id-0 collision) |
| — | `fn main(): var i=0; var total=0; while i<10: total=total+i; i=i+1; print(total)` (genuine loop reassignment, Unit return) | `45` | `45` (AFTER fix; not tested before fix but same code path) | correct after fix — direct evidence the bug is general, not match-specific |

All rows marked "silent-wrong" reproduce with **exit code 0 or a small
nonzero code, never a crash** — confirming this is a genuine silent-wrong
bug (not a loud failure) exactly as the task described, just with a
different root cause than the one suspected.

## Battery (AFTER fix, oracle-equal)

All of the following now match the oracle output exactly (module the known
pre-existing native-print-lacks-newlines quirk, and interp-side oracle
`Unknown variable: x` fallback-to-interpreter noise which the oracle itself
recovers from):

- Shape 1a/1b (`case 1: print(100); case x: print(x)`, n=1 and n=7):
  `100` and `7`.
- Shape 2 (`case x: print(x * 2)`, n=9): `18`.
- Shape 3 (binding arm listed first): `9`.
- Shape 4a/4b/4c (local / param / call-result scrutinee): `9` in all three.
- Root-cause isolation cases (`helper_unit.spl`, `rename1.spl`,
  `both.spl`, `rettype_only.spl`): all now `5` where oracle is `5`.
- Loop-reassignment case (`while_unit.spl`, Unit-return `main`, genuinely
  reassigned `i`/`total`): `45`, matching oracle.
- **Multi-construct verification program** (two matches with binding arms
  doing arithmetic on the bound name, plus one enum match with variant
  arms, in one program): oracle prints `100`,`10`,`12`,`25`; native (fixed)
  prints the same four values (concatenated `100101225` per the known
  no-newline native-print quirk) and returns exit code `147` = `100+10+12+
  25`, the correct sum. Full parity.

No regressions found: all previously-working typed-return cases
(`rettype_only.spl`, `both.spl`, existing `enum_match` etc.) still produce
identical output after the fix.

## Full smoke-matrix gate

`sh scripts/check/native-smoke-matrix.shs` — baseline (pre-fix, at commit
`f688a40fb39`): **14/15 PASS**, 0 codegen_fallback_hits, only failure
`option_nil_check` (pre-existing, allowed per the gate).

Re-run AFTER the fix (confirmed): **total=15 pass=14 fail=1 xfail=0
xpass=0 codegen_fallback_hits=0**; the single fail is `option_nil_check`
(pre-existing/allowed). Gate met (>=14/15, 0 fallback hits, only allowed
fail). Unchanged from baseline as expected: none of the matrix's 15 cases
exercise a Unit-returning entry function with a slotted local landing on
id 0 (they all use `fn main() -> i64:`), and the fix is a strict superset
of the old behavior (it only ADDS the previously-dropped Store for
written-id 0).

## Files changed

- `src/compiler/60.mir_opt/mir_opt/var_reassign_ssa.spl` — the fix
  (`ssa_alloca_apply_def_store`), 34-line diff (comment + `if`→`match`
  restructure only, no behavioral change for non-zero ids).

Patch: `scratchpad/match_binding.patch`.

## HARD RULE compliance

No loud failure was converted to silent-wrong. The fix only ADDS a
previously-missing `Store` instruction on a path that was previously
silently dropping it; every other code path (idx<0, no slot) is untouched
and still emits the exact same output as before.
