# `while true:` + `continue`/`break` silent miscompile — root cause + fix

## Worktree
`/tmp/wt_cont` pinned at `f688a40fb392efccf47ed243e498a8f257f3d408`. Binary link per
setup instructions. All builds via `env -u SIMPLE_BOOTSTRAP bin/simple native-build
--entry <file> -o <out> --clean`, executed with the pure-Simple compiler
interpreted directly from `src/compiler/*.spl` (edits take effect with no rebuild).

## Root cause

`src/compiler/50.mir/mir_lowering_stmts.spl`:

- `lower_while` (was line 741-743) and `lower_loop` (was line 706-708): after
  `self.lower_block(body)` returns, both **unconditionally** call
  `terminate_goto(cond_block)` / `terminate_goto(loop_block)` on `current_block`.
  `MirBuilder.set_terminator` (`mir_data.spl:463-472`) unconditionally
  overwrites whatever terminator is already on that block — no guard.
- If the loop body's last *top-level* statement (not nested inside a further
  `if`/`match`, which each build their own separate then/else/merge blocks) is
  itself a bare `break` or `continue`, that statement already set the
  block's terminator (`goto exit_block` for break, `goto cond_block` for
  continue). The subsequent unconditional `terminate_goto` **silently
  overwrites it**.
- Concretely: a bare trailing `break` (with nothing wrapping it in an `if`)
  gets its `goto exit_block` clobbered by `goto cond_block` — the break is
  silently turned into a loop-back, producing an **infinite loop** on a
  `while true:` (and identically on `loop:`, which desugars to
  `while true:` — `src/compiler/10.frontend/core/parser_stmts.spl:888-897`,
  using a real `expr_bool_lit(1,0)` node specifically to dodge bug #163's
  unresolved-ident issue).
- The exact same class of bug does **not** affect `for`-loops: `lower_for`
  (`mir_lowering_stmts.spl:1086-1093`) already has the correct guard, with a
  comment describing precisely this hazard:
  ```
  # Fall through into the increment block. If the body's last statement
  # already terminated the current block (an explicit break/continue/
  # return with no trailing code), don't add a second terminator -- let
  # that jump stand.
  if not b_body_end.current_block_has_explicit_terminator():
      b_body_end.terminate_goto(inc_block)
  ```
  `lower_while`/`lower_loop` never received the equivalent guard — this is
  the gap that made `continue`/`break` in `while true:`/`loop:` behave
  differently (worse) than in `for`.
- `if`/`else` (`lower_if`, same file, lines 645/665) is also already safe:
  it always creates and switches to a **fresh** merge block, so an `if` or
  `if/else` containing `continue`/`break` never lets a caller write into an
  already-terminated block — which is why "continue guarded by `if`" (the
  common, idiomatic pattern, e.g. `if i == 2: continue`) worked fine even
  before this fix. The bug requires a **bare, unwrapped** `break`/`continue`
  as the loop body's last top-level statement.

## Fix

Added the same guard `lower_for` already uses, to `lower_while` and
`lower_loop` in `src/compiler/50.mir/mir_lowering_stmts.spl`: only emit the
trailing backedge/loop-repeat `terminate_goto` if
`current_block_has_explicit_terminator()` is false. One file changed, 15
insertions / 2 deletions. See
`/home/ormastes/dev/pub/simple/scratchpad/continue_whiletrue.patch`.

A related, narrower issue was also found (not fixed, out of scope): if
`continue`/`break` is followed by more *dead* statements in the exact same
block (e.g. `if i == 2: continue; if i > 100: print(999)` — the nested `if`
is unreachable code after `continue`), `lower_block`
(`_MirLowering/function_lowering.spl:404-416`) still lowers those dead
statements unconditionally, since it has no "stop once terminated" check.
Empirically this reproduces **identically** on the oracle interpreter too
(same dead code gets executed there), so it does not cause oracle-vs-native
*divergence* — logged here for awareness, not fixed, since it's outside this
task's explicit scope (`while true:`/`continue` silent miscompile) and
touching the general `lower_block` loop is a broader change.

## Battery: oracle vs native (post-fix)

All commands compare printed value *sequences* (native `print` has no
trailing newline, per the documented native quirk); process exit codes are
known-garbage on native and ignored.

| Case | Program shape | Oracle | Native (post-fix) | Match |
|---|---|---|---|---|
| Basic repro (task's exact repro, with `print(0)` prefix) | `while true:` + `if i==2: continue` + `print(i)` + `if i>4: break` | 0,1,3,4,5 | 0,1,3,4,5 | YES |
| Basic repro, no `print(0)` workaround (literal repro) | same, `var i=0` as first stmt | (n/a, uses print(0) workaround per setup) | 1,3,4,5 | YES (correct value) |
| `loop:` (desugars to while-true) | same shape via `loop:` | 0,1,3,4,5 | 0,1,3,4,5 | YES |
| Plain conditional `while i<6:` + continue | `j==3` skipped | 1,2,4,5,6 | (combined battery) 1,2,4,5,6 | YES |
| Nested `while true` inside `while` + continue | 3x3 nested | 0,11,13,14,21,23,24,31,33,34,96 | same | YES |
| elif-continue (`if..elif..else`) | continue in both `if` and `elif` arms | 0,1,3,5,6,7,99 | same | YES |
| Divergent-value phi via continue (`i=0`→`i=100`→continue) | 3-way merge at loop header | 0,100,101,102,103,99 | same | YES |
| Triple bare-`if`-guarded continues in one loop | 3 separate `if: continue` | 0,1,3,5,7,8,9,99 | same | YES |
| **Bare unwrapped `break` as loop's last top-level stmt (THE bug)** | `while true: i=i+1; print(i); break` | 1, 99 | **PRE-FIX: infinite loop (hang, garbage exit via timeout)**; **POST-FIX: 0,1,99 (matches, with `print(0)` prefix)** | YES post-fix, NO (hang) pre-fix |
| Bare `if..else` both-arms-terminate (`continue` in `if`, `break` in `else`, last stmt) | | 1,2,3,4,5,99 | same | YES |
| for-in over array + continue (regression check) | | n/a (interpreter hangs on for+range+continue, a separate pre-existing **interpreter**-only bug, out of scope) | for-in over *range* correctly PANICs loudly (`#143`, pre-existing, unrelated); for-in over *array* passes in the official smoke matrix | n/a / OK |
| Dead code after `continue` (nested `if`, unreachable) | logged as separate narrow issue above | matches native (both wrong in the same way) | matches | n/a (not fixed, no divergence) |

## Official gate

`sh scripts/check/native-smoke-matrix.shs` (full run):
```
total=15 pass=14 fail=1 xfail=0 xpass=0 codegen_fallback_hits=0
```
Only failure: `option_nil_check` (pre-existing, allowed per task gate).
Gate requirement (`>=14/15`, `0 codegen_fallback_hits`, only allowed fail
`option_nil_check`) is met.

## Files touched
- `src/compiler/50.mir/mir_lowering_stmts.spl` — `lower_loop` and
  `lower_while`, guarded the trailing `terminate_goto` with
  `current_block_has_explicit_terminator()` (mirrors `lower_for`'s existing
  guard).

## Deliverables
- Patch: `/home/ormastes/dev/pub/simple/scratchpad/continue_whiletrue.patch`
- This report: `/home/ormastes/dev/pub/simple/scratchpad/continue_whiletrue_report.md`
- Worktree `/tmp/wt_cont` removed after patch export (not committed/pushed).
