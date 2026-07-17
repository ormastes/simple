# Interpreter diverges from native on `if val v = x.?:` and `return`-inside-value-match-arm

**Lane:** S35 (parallel bug-fix campaign, tasks #182/#183)
**Date:** 2026-07-17
**Status:** notable finding, not itself fixed — documents a pre-existing, already-known
class of interpreter bug that the S35 task brief unknowingly relied on as "ground truth".

## Summary

Tasks #182 ("value-position match always takes the first arm") and #183
("option_nil_check smoke case returns rc=1 instead of 7") were both handed to
lane S35 as verified-open silent-wrong-answer bugs in **native codegen**.
After a 23-probe matrix (17 for #182, 6 for #183; see below) exercising int
and enum scrutinees, sparse/dense int dispatch, tail-expr and `return`-form
matches, nested matches, enum payloads, `Option` params/returns/none-cases,
and nested `if val`, **native codegen produced the mathematically correct
answer on every single probe.** Both bugs are already fixed on this worktree's
tip (`be3ac62df6c8e2b2b6f2a776cdf02978b82f0663`):

- **#182** fixed by `f10db44f0f477e839562654672a1531d58c881c4`
  ("fix(mir): don't clobber return terminators in int-match arm dispatch",
  2026-07-13) in
  `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`
  (`emit_switch_dispatch`/`emit_if_chain_dispatch`).
- **#183** fixed by `5a63936b50e430c9036cbb698f410d41a91cf5bc`
  ("fix(mir): .? extracts Option payload (was bare rt_is_some bool) — matrix
  15/15", 2026-07-14) in
  `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:1829`
  (`ExistsCheck` case).

Both commits are ancestors of the worktree tip (`git merge-base --is-ancestor`
confirmed for both). The task brief's "verified open as of today" is almost
certainly explained by the finding below: **the interpreter, used as the
task's prescribed oracle, is itself wrong for exactly these two constructs**,
so a naive interp-vs-native diff still looks like an open native bug even
though native has been correct since 2026-07-13/14.

## The actual finding: interpreter is not ground truth for `.?` / `if val` / `return`-in-match-arm

1. **`if val v = x.?:` (option_nil_check shape).** The interpreter
   (`env -u SIMPLE_BOOTSTRAP bin/simple run <probe>.spl`) returns **rc=0**
   for `val x: i64? = 7; if val v = x.?: return v; return 0` — i.e. it never
   takes the `if val` true branch even though `x` is present. This matches
   the already-documented interpreter landmine referenced (but never
   independently filed) in
   `src/compiler/50.mir/mir_lowering_stmts.spl:499-511` and `:537-541`
   ("the documented `if val`/`if not x.?` quirk", "Bug
   native_i64opt_some0_collapses_to_nil's class of issue") and in this
   session's own memory
   (`reference_interpreter_dict_and_value_quirks.md`: "`.?` on 0-i64→false").
   This session's probes show the breakage is not limited to the `0`-payload
   case — it reproduces at `x=7`, on params, and on function-returned
   Options. Native gets every one of these right (see matrix below).

2. **`return` inside a value-position match arm.** For
   ```
   fn pick(n: i64) -> i64:
       val r = match n:
           case 2: return 7
           ...
       return r + 1
   fn main() -> i64: return pick(2)
   ```
   the interpreter treats the arm's `return 7` as merely supplying `r`'s
   value and then **keeps executing** — `pick(2)` returns `8` (`r+1`), with
   a print-instrumented run confirming `print`s placed *after* the match
   block execute. Native codegen correctly treats `return` as a real
   function-exiting terminator (per `f10db44f0f4`'s explicit intent: "don't
   clobber return terminators") and returns `7`, exiting `pick` immediately.
   Ordinary `return` semantics (exit the enclosing function unconditionally)
   make native's answer the only defensible one; nothing in the language
   docs suggests `return` means something different inside a match arm used
   as a value.

## Consequence / guidance for other lanes

- **Do not add `.?` / `if val` / `return`-inside-value-match-arm cases to
  `scripts/check/check-native-seed-parity.shs`-style interp-vs-native diff
  tooling without an explicit `xfail` on the interpreter side** — the
  interpreter itself is the broken side for these three shapes, so a strict
  parity check would either falsely flag native or need to special-case the
  known-bad oracle.
- Ordinary value-position match on plain (non-`return`) arm bodies, int and
  enum scrutinees, nested matches, and enum-payload matches all agree between
  interpreter and native and are safe for parity-style checks.
- Added two native-only regression-guard cases to
  `scripts/check/native-smoke-matrix.shs` (cases 16/17,
  `write_case_match_value` / `write_case_match_value_return`) so any future
  regression of the `f10db44f0f4` fix is caught without depending on the
  interpreter.
- This interpreter bug itself was left unfixed (out of scope for S35's native
  codegen mandate; fixing it would mean touching the seed/self-hosted
  interpreter's `if val`/Option-check and `return`-signal-propagation paths,
  a different subsystem). Filing here per the task's "notable finding beyond
  these two bugs" instruction so it doesn't get silently re-discovered.

## Probe matrix (all on worktree tip `be3ac62df6c`, fresh filenames, LLVM backend)

### #182 — value-position match (17 probes, all PASS on native)

| # | Shape | Oracle | Native | Match? |
|---|-------|-------:|-------:|:------:|
| 1 | int sparse (2 arms + wildcard), n=2 | 200 | 200 | yes |
| 2 | int dense (4 arms + wildcard), n=3 | 30 | 30 | yes |
| 3 | tail-expr (no `val r=`, implicit fn-body return) | 200 | 200 | yes |
| 4 | `return match n: ...` | 200 | 200 | yes |
| 5 | enum bare-variant scrutinee | 2 | 2 | yes |
| 6 | multi-statement arm bodies | 200 | 200 | yes |
| 7 | multiple calls, varying n (1/2/5) | 100,200,999 | 100,200,999 | yes |
| 8 | called in a `while` loop, summed | 88 (=600 mod 256) | 88 | yes |
| 9 | enum with payload (`Circle(i64)`/`Square(i64)`) | 90 | 90 | yes |
| 10 | nested match-in-match-arm | 21 | 21 | yes |
| 11 | match without wildcard (no default) | loud compile error | loud compile error (same message) | yes (correctly rejected, not silent) |
| 12 | `Or` pattern (`case 1 \| 2:`) | 188 (=700 mod 256) | 188 | yes |
| 13 | plain-binding default arm (`case x: x+1000`) | 185 | 185 | yes |
| 14 | match value used inline in another expr (`1 + match ...`) | 201 | 201 | yes |
| 15 | **arm body = bare `return N` (sparse, f10db44f0f4 shape)** | 201 (interp bug, see above) | **200 (correct)** | **no — interpreter is wrong, native is right** |
| 16 | **arm body = bare `return N` (dense, 4+ arms)** | 31 (interp bug) | **30 (correct)** | **no — same divergence** |
| 17 | print-instrumented `return`-in-arm (diagnostic only) | continues past `return` (interp bug) | n/a (diagnostic) | confirms #15/#16 |

### #183 — `.?` / Option (6 probes, all PASS on native; oracle wrong on all 6)

| # | Shape | Oracle | Native | Expected (manual) |
|---|-------|-------:|-------:|-------------------:|
| 1 | baseline smoke-matrix shape, x=7 | 0 (bug) | 7 | 7 |
| 2 | x=nil | 0 (bug, but coincidentally = expected) | 5 | 5 |
| 3 | param, present (9) | 0 (bug) | 9 | 9 |
| 4 | param, nil | 0 (bug, coincidentally right) | 5 | 5 |
| 5 | Option from fn return, present | 0 (bug) | 9 | 9 |
| 6 | two nested `if val`, both present | 0 (bug) | 10 | 10 |

## Verification commands

```
cd /home/ormastes/dev/wt_repro2
git merge-base --is-ancestor f10db44f0f477e839562654672a1531d58c881c4 HEAD && echo ok  # #182 fix is ancestor
git merge-base --is-ancestor 5a63936b50e430c9036cbb698f410d41a91cf5bc HEAD && echo ok   # #183 fix is ancestor
sh scripts/check/native-smoke-matrix.shs   # total=17 pass=17 fail=0 codegen_fallback_hits=0
```

No native-compiler code changes were made — both #182 and #183 were already
fixed. Only `scripts/check/native-smoke-matrix.shs` was extended (cases
16/17) to guard the #182 fix going forward, plus this doc.
