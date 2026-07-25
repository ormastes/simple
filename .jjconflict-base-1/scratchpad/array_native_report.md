# Array mutation on the NATIVE --entry path — characterization + fix

Worktree: `/tmp/wt_arr` (base `228ed617cad`, sanity `print(41)` build OK, no fetch needed).
Oracle: `env -u SIMPLE_BOOTSTRAP bin/simple run p.spl` (interpreter). Native: `bin/simple native-build p.spl -o bin && ./bin` (no newlines between prints; digits are read positionally).

## Root cause (one bug, one file)

`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`, the `method == "push"` MIR-lowering
arm (~line 845), built the value handed to `rt_array_push` by hand: it special-cased only
raw string literals (`rt_strlen`/`rt_string_new`, duplicating `box_runtime_value`'s own str
branch) and passed every other operand — int/bool/float literals, and already-tagged
values — through **raw, untagged**.

Every other array/dict element producer (`lower_array_lit`'s per-element loop,
`lower_dict_lit`'s value slot, `lower_dict_key`) instead calls the shared
`self.box_runtime_value(local)` helper (`expr_dispatch.spl:119`), which tag-shifts a raw
int/char by `<<3` (matching the reader-side `>>3` untag in `decode_runtime_value` and in
every `a[i]` index-read lowering) — the runtime's universal "ANY" tagged-value ABI. `push`
never did this, so:

- `a.push(7)` stores raw `7` into the array's backing i64 slot.
- Reading it back (`a[i]`, which always un-tags via `ashr i64 %v, 3`) computes `7 >> 3 == 0`.
- Any pushed literal `< 8` is silently corrupted to `0`; larger literals are corrupted to
  `wrong_value >> 3` (not merely "sometimes zero" — deterministically wrong, always).
- `.len()` / `rt_array_push`'s realloc/append bookkeeping (verified in
  `src/runtime/runtime_native.c: rt_array_push`/`rt_core_array_reserve`) is completely
  correct — length and capacity always advance right. Only the stored payload for a
  **pushed** (not literal-initialized) element is wrong.

Confirmed by dumping the actual LLVM IR emitted for `a.push(7)` (temporary instrumentation
in `llvm_codegen_adapter.spl::llvm_compile_module_direct`, reverted before producing the
final patch): literal elements go through `shl i64 %v, 3` before `rt_array_push`; the pushed
element's IR was bare `%l10 = add i64 7, 0 ; const int` straight into
`call i8 @rt_array_push(ptr %l9, i64 %l10)` — no shift.

## Fix

Replace the hand-rolled string-only tagging block with the same call every other producer
uses: `val push_val_tagged = self.box_runtime_value(push_val_raw)`. `box_runtime_value` is
itself idempotent for already-tagged runtime/array/dict/nil locals (early-return on
`runtime_value_locals.has(...)`), so this is a pure drop-in — no double-tagging risk for
argv/variable values that already carry a tagged representation.

Net diff: -32/+19 lines in one file (`method_calls_literals.spl`), no other file touched.
FENCED FILE: this lowering lives entirely inside `method_calls_literals.spl`, which is on
the owned-file fence list. Per the task's fence rule the fix is delivered as a
**CONFLICT-FLAGGED** patch (`scratchpad/array_native.patch`), verified correct in the
isolated `/tmp/wt_arr` worktree but not applied to the main tree — the owning lane should
review/land it (or the caller can apply it directly; it is a strict subset of one `if`
arm, low collision risk with the ownership list's likely concerns which are elsewhere in
that file: map/filter/fold/join/writeback plumbing above this arm is untouched).

## Characterization matrix (oracle vs. native, BEFORE fix / AFTER fix)

All values below are the concatenated single-digit `print()` output (native has no
newlines); "→" separates oracle / native-before-fix / native-after-fix.

| # | Case | Oracle | Native BEFORE | Native AFTER | Verdict before → after |
|---|------|--------|----------------|---------------|------------------------|
| 1 | `a=[1,2]; a=a.push(7); print(a.len(),a[2])` | `3,7` | `3,0` | `3,7` | **silent-wrong → CORRECT** |
| 2 | `a=[1,2]; a.push(7)` (no reassign) `; print(a.len())` | `3` (push mutates the shared heap handle in place — array "value semantics" in this language means *copy on pass*, not *no aliasing of the underlying push*; the reassignment idiom is stylistic, not required for push to take effect) | `3` | `3` | CORRECT → CORRECT (unaffected, already right) |
| 3 | `a=[1,2,3]; a[0]=9; print(a[0],a[1],a[2])` | `9,2,3` | `9,2,3` | `9,2,3` | CORRECT → CORRECT (unaffected) |
| 4 | `.len()` after literal, after push+reassign | `3,4` | `3,4` | `3,4` | CORRECT → CORRECT (length bookkeeping was always right; only the payload was wrong) |
| 5 | `a=[1,2,3]; print(a[10])` (OOB read) | **silent-wrong**: interpreter/oracle itself returns `len()` (3) for ANY OOB index (3,4,100 all read back as `3`) — a pre-existing ORACLE bug, out of this task's native-only scope, noted here for the record only | loud `PANIC: bounds_check intrinsic index=10 len=3`, exit!=0, no further output | same loud panic (unchanged — untouched by this fix) | native already LOUD (acceptable per task's hard rule); oracle is silent-wrong but out of scope |
| 6 | `[Point(x:1,y:2), Point(x:3,y:4)]`; `a[0].x` read then `a[0].x=5` write | `1,5` | `1,5` | `1,5` | CORRECT → CORRECT (unaffected — struct-array element field r/w never went through `push`) |
| 7 | `for x in a: sum+=x` after `a=a.push(4)` on `[1,2,3]` | count=4, sum=`10` | count=4 (**len correct**), sum=`6` (**silent-wrong**: pushed element read as 0 mid-iteration) | count=4, sum=`10` | **silent-wrong → CORRECT** |
| multi | push×2 + index-write + len + full iterate in one `main` | `4,99,2,7,42,150` | not tested standalone (same bug class as #1/#7 would have corrupted 2 of 4 elements) | `4,99,2,7,42,150` | CORRECT after fix |

Additional pinpoint tests run during root-causing (not in the table above, same
before/after pattern): pushing a `val`-bound variable (`val seven=7; a=a.push(seven)`) hit
the identical bug (native-before: `3,0`; native-after: `3,7`) — confirms the bug is not
literal-constant-folding-specific, it is the push lowering itself.

## Hard-rule compliance

- No loud failure was weakened to silent-wrong. The OOB `bounds_check` panic path
  (case 5) is untouched by the diff and still hard-panics with a clear message and
  non-zero worker exit.
- Fenced files (`function_lowering.spl`, `module_assembly.spl`, `switch_operators_calls.spl`,
  `mir_lowering_stmts.spl`, `parser_stmts.spl`, `primary_expr.spl`, `var_reassign_*.spl`,
  `20.hir/statements.spl`+`expressions.spl`, `aggregate_intrinsics.spl`) were read-only
  referenced for characterization (to locate `box_runtime_value`/`lower_array_lit`'s boxing
  idiom) but never edited. `method_calls_literals.spl` (also fenced) is the one file
  touched — delivered as a flagged patch per the fence rule, not applied to `main`.

## Verification run

- All 7 characterization cases + the multi-construct case rebuilt and rerun after the fix;
  every native output now matches the oracle byte-for-byte (see table).
- `sh scripts/check/native-smoke-matrix.shs` against the fixed worktree:
  **total=15 pass=14 fail=1 xfail=0 xpass=0 codegen_fallback_hits=0** — the single FAIL is
  `option_nil_check` (rc 1 vs want 7), the known pre-existing baseline failure the task
  explicitly allows. `for_in_array` (rc 15/15) and `array_index_rw` (rc 71/71) both PASS —
  no regression. Full log copied to `scratchpad/smoke_matrix_after_fix.log`.

## Deliverables

- `scratchpad/array_native.patch` — the fix, isolated to `method_calls_literals.spl` (fenced;
  CONFLICT-FLAGGED, not applied to `main`).
- `scratchpad/array_native_report.md` — this report.
- Worktree `/tmp/wt_arr` removed after patch export.
