# Pure-Simple Divergence Sweep (2026-07-29)

Read-only continuation of `pure_simple_fix_plan_2026-07-29.md`'s known 6-bug
family. Method: `bin/simple` here is the **Rust bootstrap seed** (stderr banner
confirms it), so "JIT" below is the seed's Cranelift JIT — a proxy for what the
pure-Simple native-AOT backend may also get wrong, per the task brief. Oracle =
`SIMPLE_EXECUTION_MODE=interpreter bin/simple run probe.spl`; suspect = default
`bin/simple run probe.spl`. 35 probes across float/int formatting, nested
aggregates, string escaping, bool/None/nil printing, array join/print, char/byte.

Known-6 (NOT re-reported except where a nested/new context changes behavior):
tuple print, dict print, enum print, object print, method-result raw-int, bool
1/0, join-empty-(ints), array-methods-gap.

## Results table

| probe | oracle output | JIT output | diverges? | category | severity |
|---|---|---|---|---|---|
| p17_none_print (`Option<i64> = None; print(x)`) | `Option::None` | *(blank line)* | **YES — NEW** | Option/nil printing | **HIGH** |
| p19_array_with_nil (`[Some(1), None, Some(3)]`) | `[Option::Some(1), Option::None, Option::Some(3)]` | `[<enum@0x...>, nil, <enum@0x...>]` | **YES — NEW variant** | Option/nil printing (array context) | HIGH |
| p10_dict_of_tuples | `{a: (1, 2), b: (3, 4)}` | `<dict@0x...>` | yes (known: dict print) | nested variant only | — |
| p11_array_of_dicts | `[{x: 1}, {y: 2}]` | `[<dict@0x...>, <dict@0x...>]` | yes (known: dict print) | nested variant only | — |
| p12_tuple_of_arrays | `([1, 2], [3, 4])` | `<tuple@0x...>` | yes (known: tuple print) | nested variant only | — |
| p18_some_print (`Option<i64>`) | `Option::Some(42)` | `<enum@0x...>` | yes (known: enum print) | nested variant only | — |
| p20_array_floats_join | `1.0,2.5,3.75` | `,,` | yes (known: join-empty) | confirms join bug extends to floats | — |
| p21_array_bools_join | `true,false,true` | `,,` | yes (known: join-empty) | confirms join bug extends to bools | — |
| p25_result_ok_print | `Result::Ok(5)` | `<enum@0x...>` | yes (known: enum print) | nested variant only | — |
| p26_result_err_print | `Result::Err(bad)` | `<enum@0x...>` | yes (known: enum print) | nested variant only | — |
| p27_enum_struct_payload (`Shape.Circle(radius: 2.5)`) | `Shape::Circle(2.5)` | `<enum@0x...>` | yes (known: enum print) | nested variant only | — |
| p28_option_of_tuple | `Option::Some((1, 2))` | `<enum@0x...>` | yes (known: enum+tuple print) | nested variant only | — |
| p30_dict_float_values | `{a: 1.5, b: 2.5}` | `<dict@0x...>` | yes (known: dict print) | nested variant only | — |
| p33_array_of_tuples | `[(1, x), (2, y)]` | `[<tuple@0x...>, <tuple@0x...>]` | yes (known: tuple print) | nested variant only | — |
| p01_float_zero (`3.0`) | `3.0` | `3.0` | no | float fmt | — |
| p02_float_neg (`-3.14`) | `-3.14` | `-3.14` | no | float fmt | — |
| p03_float_exp (`1e10`) | `10000000000.0` | `10000000000.0` | no | float fmt | — |
| p04_float_add (`0.1+0.2`) | `0.30000000000000004` | same | no | float fmt | — |
| p05_float_div (`1.0/3.0`) | `0.3333333333333333` | same | no | float fmt | — |
| p06_int_neg (`-5`) | `-5` | `-5` | no | int fmt | — |
| p07_int_i64_max | `9223372036854775807` | same | no | int fmt | — |
| p08_int_i64_min | `-9223372036854775808` | same | no | int fmt | — |
| p09_int_hex (`0xFF`) | `255` | `255` | no | int fmt | — |
| p13_str_quotes | `she said "hi"` | same | no | string escaping | — |
| p14_str_newline | 2 lines | same | no | string escaping | — |
| p15_str_unicode (ascii) | `hello world cafe` | same | no | string | — |
| p15b_str_unicode2 (`\u{e9}`,`\u{4e16}\u{754c}`) | `café 世界` | same | no | unicode escapes | — |
| p16_bool_true (`print(true)`) | `true` | `true` | no | bool literal (contrast w/ known bool-*method*-1/0 bug) | — |
| p22_array_strings_join | `x,y,z` | same | no | join | — |
| p23_array_floats_print | `[1.0, 2.5, 3.75]` | same | no | array print | — |
| p24_char_print (`'a'`) | `a` | `a` | no | char | — |
| p29_byte_print (`u8 = 65`) | `65` | `65` | no | byte | — |
| p31_neg_float_in_array | `[-1.5, 2.5, -3.0]` | same | no | array print | — |
| p32_string_with_tab | `a\tb` (literal tab) | same | no | string escaping | — |
| p34_i32_min_max | 2 lines, both correct | same | no | int fmt | — |
| p35_float_to_string_concat | `value: 3.14` | same | no | `.to_string()` + concat | — |

**New divergences found (not covered by the known 6, or behaving differently
enough to warrant a distinct entry): 2** (p17, p19). All other diverging probes
are nested/contextual re-expressions of the already-tracked tuple/dict/enum/join
bugs and are listed only to confirm they extend to floats, bools, and
user-defined enum payloads.

## Ranked shortlist — highest-value NEW gaps

1. **Bare `Option::None` prints as an empty line, not `Option::None` or even an
   address placeholder (p17).** Severity HIGH: unlike the known enum-print bug
   (which at least visibly shows `<enum@ptr>`, an obvious "something's wrong"
   signal), this is a **silent** failure — a None-check gone wrong looks like a
   blank print, easily mistaken for legitimate empty output. Root cause is very
   likely the dual Option ABI documented in
   `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:1619-1653`
   (`lower_try_expr`'s docstring): the "flat-nullable" Option representation
   stores `None` as raw nil/0, which `lower_bootstrap_print_call`
   (`switch_operators_calls.spl:902` on) then passes through as if it were a
   `char*`/string local (its numeric-vs-string coercion logic only special-cases
   int/float/bool locals, not the nil/Option sentinel) — printing a null/empty
   string instead of routing through the enum formatter. **Likely fix site:**
   `switch_operators_calls.spl` `lower_bootstrap_print_call` (~902-935), add an
   explicit `option_value_locals`-tracked-and-nil arm that renders
   `Option::None` before falling to the generic numeric/string coercion, mirror
   the interpreter's oracle rendering.

2. **`None` renders inconsistently depending on context — blank alone (p17) vs.
   literal `nil` inside an array (p19).** Severity HIGH: two different silent
   representations for the same value is worse than one, and neither matches the
   oracle's `Option::None`. This means any code path building an
   `Array<Option<T>>` and printing it for debugging gets literally the word
   `nil` where a real `None` sits, indistinguishable from a null/uninitialized
   local. Also note `Some(v)` inside the same array correctly resolves to the
   *enum* representation (`<enum@ptr>`, matching the known bug) rather than the
   *flat* representation — meaning the array-element formatter and the
   bare-local formatter disagree with each other on which of the two ABIs
   (flat-nullable vs boxed-enum) a given `Option` local is using. **Likely fix
   site:** same file, plus wherever array/aggregate element formatting resolves
   each element's runtime representation (search `rt_array_join_any` /
   `rt_to_string` callers in `src/runtime/runtime_native.c` and the aggregate
   print-routing arms noted in the known-6 plan at
   `switch_operators_calls.spl:953-967`) — the element formatter needs the same
   `option_value_locals`-nil-aware arm as bare-local printing, so both paths
   converge on one representation.

3. **`join()` on floats and bools reproduces the known ints-only join bug
   (p20, p21) — confirms it is receiver-type-agnostic, not int-specific.** Not
   new in kind, but worth folding into the existing fix's regression coverage
   (`runtime_native.c:3142` `rt_array_join_any`, per the fix plan) — the fix
   plan's probe set only exercised `[1,2,3].join(",")`; add float/bool array
   join probes to its verification list so the eventual fix isn't validated on
   ints alone and silently still broken for floats/bools.

## Report

Path: `doc/08_tracking/bug/pure_simple_divergence_sweep_2026-07-29.md`
