# Native path: string `<`/`>`/`<=`/`>=` compare raw tagged-string handles, not lexicographic content

**Date:** 2026-07-17
**Severity:** High (silent wrong output, no diagnostic)
**Status:** open
**Task:** #178 native text interpolation + string ops verification round 2 (lane S47)

## Symptom

String equality (`==`, `!=`) is correct on the native path (already fixed by
task #148, per lane context). Ordering comparisons are not.

```simple
fn main():
    val a = "abc"
    val b = "abd"
    print "X1:{a < b}|END"
    print "X2:{a > b}|END"
    print "X3:{b > a}|END"
```

- Oracle: `X1:true|ENDX2:false|ENDX3:true|END` (correct lexicographic order:
  "abc" < "abd")
- Native: `X1:false|ENDX2:true|ENDX3:false|END` — every relation is flipped
  relative to the oracle in this probe.

Additional probe with equal strings (`a = "abc"`, `c = "abc"`):

- `a <= c`: oracle `true`, native `true` (both agree, coincidentally, since
  equal-pointer-vs-equal-content collapse the same way here)
- `a >= c`: oracle `false` (!), native `true` — the two paths disagree here as
  well, in the *opposite* direction, which is further evidence this isn't a
  simple sign flip but two genuinely different comparison semantics (oracle:
  unclear if its own `>=` handling for strings is fully consistent either;
  native: comparing something other than string content).

## Root cause (found via code read)

`grep` across `src/compiler/50.mir/_MirLoweringExpr/*.spl` and
`src/runtime/*.c` for `rt_string_compare` / `rt_strcmp` / `strcmp` returns
**zero hits in the MIR lowering layer**. `switch_operators_calls.spl`
(~line 509-535, `lower_binop`) maps HIR `Lt`/`LtEq`/`Gt`/`GtEq` directly to
`MirBinOp.Lt`/`Le`/`Gt`/`Ge` with **no receiver-type check at all** — unlike
`Eq`/`NotEq` (string equality), which elsewhere in the codebase has dedicated
tagged-string-aware handling. Since a `text` value is represented as a tagged
heap-string handle (not a raw byte buffer inline), a raw `MirBinOp.Lt`/`Gt` on
two string operands compares the **handle/pointer bit patterns** — arbitrary
relative to allocation order, not the string's lexicographic content. No
`rt_string_compare`-style runtime function exists to call.

## Expected

`<`, `<=`, `>`, `>=` on two `text` operands must perform a real byte-wise (or
codepoint-wise — needs a decision, matching whatever the oracle does)
lexicographic comparison of content, exactly like `==`/`!=` already do for
strings after task #148's fix.

## Suggested direction

- Add a runtime string-compare function (e.g. `rt_string_compare(a, b) ->
  i64` returning `-1`/`0`/`1`, à la C `strcmp`/Rust `Ordering`) if one does
  not already exist under a different name.
- In `switch_operators_calls.spl`'s `lower_binop`/binop-lowering call site,
  detect a string-typed operand (mirroring the existing `ensure_tagged_str`
  / `local_is_str` detection used throughout `method_calls_literals.spl`) and
  route `Lt`/`Le`/`Gt`/`Ge` through `rt_string_compare` + a threshold check,
  instead of the generic numeric/pointer `MirBinOp`.
- Verify against the oracle's own `<=`/`>=` behavior on equal strings before
  assuming strict `strcmp`-style semantics — the oracle's `X5` result above
  (`a >= c` = `false` for equal `a`/`c`) suggests the oracle's own ordering
  operators may have edge-case quirks worth matching exactly rather than
  "fixing" to the mathematically expected result.

## Verification

- Reproduced on worktree `/home/ormastes/dev/wt_r_find_infer` at tip
  `ffc0c360ba4` (fetched 2026-07-17), using
  `env -u SIMPLE_BOOTSTRAP bin/simple run` (oracle) and
  `env -u SIMPLE_BOOTSTRAP -u SIMPLE_RUNTIME_PATH bin/simple native-build`
  (native).
- Confirmed via direct source read that no string-aware comparison path
  exists anywhere in the MIR binop lowering for relational operators.
