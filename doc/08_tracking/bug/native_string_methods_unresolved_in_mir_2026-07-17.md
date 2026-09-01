# Native path: `.parse_f64()` and `.to_upper()` unresolved in MIR lowering

**Date:** 2026-07-17
**Severity:** Medium (loud build failure, not silent-wrong; but a real
functionality gap vs. the oracle)
**Status:** SOURCE FIXED (current Cranelift execution pending)
**Task:** #178 native text interpolation + string ops verification round 2 (lane S47)

## Symptom 1 — `.parse_f64()`

```simple
fn main():
    val a = "3.14".parse_f64()
    print "F1:{a}|END"
```

- Oracle: `F1:3.139999999999997|END` (works; the trailing-digits artifact is
  the oracle's own float-parse rounding behavior, not a bug — just the
  baseline to match).
- Native (`native-build`, `SIMPLE_BOOTSTRAP` unset): fails to build:
  ```
  [mir-lower] WARNING: unresolved method call 'parse_f64' lowered to const-0 placeholder (silent-null risk, Task #145)
  [ERROR] MIR error: MIR lowering error: unresolved method call: parse_f64
  error: MIR lowering error: unresolved method call: parse_f64
  ```

`.parse_int()`/free-function `int(...)` both work correctly natively
(regression-checked in the same sweep, no divergence there).

## Symptom 2 — `.to_upper()`

```simple
fn main():
    val s = "Hello"
    print "UP:{s.to_upper()}|END"
```

- Native (`native-build`, `SIMPLE_BOOTSTRAP` unset): fails to build with the
  identical shape:
  ```
  [mir-lower] WARNING: unresolved method call 'to_upper' lowered to const-0 placeholder (silent-null risk, Task #145)
  [ERROR] MIR error: MIR lowering error: unresolved method call: to_upper
  error: MIR lowering error: unresolved method call: to_upper
  ```

Confirmed via source read: `src/compiler/50.mir/_MirLoweringExpr/*.spl`
(the native MIR-lowering layer used by `native-build`) has no `to_upper`/
`upper` dispatch arm anywhere, unlike `to_lower`/`lower`, which are handled
alongside `trim`/`replace`/`split` (`method_calls_literals.spl` ~line 1736).
`to_upper` **is** handled in the older `cg_expr.spl` codegen path and in the
tree-walking interpreter (`eval_methods.spl` line 452), which is why it is
absent specifically from the MIR/native-build path, not from the language as
a whole.

**Note on the oracle's own `.to_upper()`:** re-verified in isolation
(`"Hello World".to_upper()` on `bin/simple run`) — the oracle prints `Hello
World` unchanged, i.e. the seed's own `to_upper()` is a no-op. This looks like
a pre-existing limitation of the feature-incomplete bootstrap seed itself,
not a native regression, so no oracle-side value comparison is possible for
this method; only "does native-build succeed at all" was checked here. Not
filed separately — the seed is bootstrap-only per repo convention and this
lane's mandate is native-vs-oracle parity for the native (pure-Simple) path.

Both failures are **loud** (correctly so, per the existing Task #145
"silent-null risk" guard converting unresolved calls into hard errors rather
than silently emitting a placeholder) — filed as functionality gaps, not
silent-wrong-answer bugs.

Note: this is a different symptom from the older, already-tracked
`pure_simple_text_split_lines_missing_2026-07-13.md`-style "seed oracle lacks
a recently-landed native feature" pattern — here it is the **reverse**: the
oracle has the feature (or a no-op stand-in, for `to_upper`), native's MIR
lowering does not resolve the call at all.

## Expected

`.parse_f64()` should resolve to a real runtime float-parse call
(`rt_string_to_f64`/similar) in native MIR lowering, matching the oracle's
behavior including its rounding characteristics. `.to_upper()` should resolve
to `rt_string_to_upper` (already declared for the LLVM backend in
`src/compiler/70.backend/backend/llvm_lib_translate.spl` line 396 — the
runtime symbol exists, only the MIR dispatch arm is missing).

## Suggested direction

Add `method == "parse_f64"` and `method == "to_upper"` handling arms in
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`, alongside
the existing `find`/`replace`/`trim`/`lower`/`to_lower` dispatch table
(~line 1777), calling `rt_raw_f64_to_string`'s parse-side counterpart for
`parse_f64` and the already-declared `rt_string_to_upper` for `to_upper` —
mirroring exactly how `to_lower` is already wired in the same arm.

## Verification

- Reproduced on worktree `/home/ormastes/dev/wt_r_find_infer` at tip
  `ffc0c360ba4` (fetched 2026-07-17), using
  `env -u SIMPLE_BOOTSTRAP bin/simple run` (oracle) and
  `env -u SIMPLE_BOOTSTRAP -u SIMPLE_RUNTIME_PATH bin/simple native-build`
  (native).

## Addendum 2026-09-01: `.upper()`, plain-expression `.chars()`, `.to_float()` — same class, fixed

Third instance of the class. All three failed at MIR lowering with
`unresolved method call:` on a directly-typed `text` receiver (no `any`
erasure), while the interpreter accepted them. Fixed in the text-special
arm of `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`:

| method | runtime symbol | semantics chosen (= interpreter) |
|---|---|---|
| `upper` | `rt_string_to_upper` (runtime.h:686, collections.rs:4157) | exact alias of `to_upper` (interpreter_method/string.rs:79) |
| `chars` (expression position) | `rt_string_chars` (runtime.h:403, collections.rs:3970) | array of 1-codepoint strings; result flagged `runtime_array_locals` + HIR `Array(Str)` |
| `to_float` | `rt_string_to_float` (runtime.h:687, collections.rs:4259) then unbox `rt_value_as_float` (runtime.h:342, value_ops.rs:91) | TOTAL: trims, 0.0 on parse failure (string.rs:447) — unlike nullable `parse_f64` |

**Empty-concat root cause (WIP commit `d260c9246e2`):** the WIP branch's
`mir_lowering_stmts.spl` for-in lane predated the `element_type_from_hir`
repair (zero grep hits on that branch), so `for c in s.chars()` elements
typed as i64 and the accumulation never emitted a string concat — output
came out empty, silently. Current main carries the repair; with the chars
arm recording `Array(Str)`, the loop lowers to
`rt_string_chars` → `rt_array_len`/`rt_array_get` → `rt_strcat_tagged`
(verified in-process against the real MIR lowering, Windows seed
md5 `f9bf124d933a0de0af5d999444234996`).

**Deliberate divergence, still open:** `int.to_float()`
(interpreter_method/primitives.rs:31) stays LOUD natively — the text arm
requires a proven Str receiver; routing an int through `rt_string_to_float`
would be silent garbage. Needs a numeric-conversion arm.

**Live census (lowered, not grepped), 2026-09-01:** interpreter-accepted
zero-arg methods still without any MIR arm: text 12/25 probed (capitalize,
title, swapcase, reversed, is_empty, char_count, to_int, parse_int,
trim_start, trim_end, chomp, ord), i64 17/19 probed (abs, to_float, floor,
ceil, round, sqrt, is_even, is_odd, to_hex, to_bin, to_oct, bit_length,
count_ones, trailing_zeros, signum, fract, to_str).

Specs (both green on Windows, engine parity verified interpreter vs
cranelift-jit via `[engine-receipt]`):
- `test/01_unit/compiler/mir/text_upper_chars_to_float_mir_lowering_spec.spl` (defect repro + empty-concat pin)
- `test/01_unit/compiler/mir/text_number_method_mir_arm_census_spec.spl` (class generalization census)
