# Native: user method named like a builtin is lowered as the builtin

Date: 2026-11-18
Target: pure-Simple MIR lowering (`release/1.0.0`), found on Stage 2 cranelift, aarch64 Linux
Status: FIXED at MIR level (seed-interpreted lowering); native re-check needs a Stage 2 rebuilt from this source

## Symptom

```simple
class Flight:
    waiters: i64

    fn join(key: text) -> Flight:
        Flight(waiters: self.waiters + key.len())

fn main():
    val flight = Flight(waiters: 4).join("abc")
    print "flight={flight.waiters}"
```

`native-build` exits 0. The binary prints `rejected invalid array handle` and
dies with SIGSEGV. The seed interpreter prints `flight=7`.

## Which names, which receivers

Measured by lowering one module per case with the seed-interpreted MIR
lowering and counting calls to the user method. 108 builtin-looking
name/arity pairs, on a class and on a struct, with text and with i64
arguments, over nine receiver forms.

| user method | lowered instead as | receiver forms hit |
|---|---|---|
| `join(x)` | `rt_array_join_any` | constructor temporary, call result, field, array element |
| `char_at(i)` | `rt_interp_cstr` + `spl_str_slice` | same four |
| `index_of(a, b)`, `find(a, b)`, `find_str(a, b)` | `rt_text_find` | same four |
| `len()`, `length()` | `rt_string_char_count` | constructor temporary only |

Class and struct behave the same, and the argument type does not matter.
A receiver that is a variable (`val`, parameter, inferred `val`, `if val`
binding, `for` binding) was never affected. Every other name in the table
(`push`, `get`, `contains`, `split`, `starts_with`, `trim`, `replace`,
`slice`, `map`, ...) already reached the user method on all nine forms.

## Root cause

`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`,
`lower_method_call`. A method call on a non-variable record receiver arrives
as `MethodResolution.Unresolved`; the user owner is only known after the
receiver is lowered (`struct_value_syms`), which the unresolved arm of
`lower_method_call_by_resolution_v1` does. Four builtin fallbacks run before
that arm and gate on the method name, the argument count and `Unresolved`
only:

- `try_lower_text_join_v1` (`join`, 1 arg),
- `try_lower_text_char_at_v1` (`char_at`, 1 arg),
- the `index_of`/`find`/`find_str` 2-arg arm of
  `try_lower_text_search_and_transform_v1`, which does test
  `predicate_has_custom_owner`, but that flag was only computed for
  `starts_with`/`ends_with`/`contains`,
- the `len`/`length` unresolved arm, which lowers the receiver and then
  picks `rt_len`/`rt_string_char_count` without looking at its owner.

Release commit `2065a344022` (#10064) is not involved. It changed the Rust
seed's Cranelift dispatch of an erased-receiver `.join(sep)` and touched no
pure-Simple lowering; this defect is the same before and after it.

## Fix

Before the four fallbacks the receiver is lowered once and its recorded
owner is asked for the method (`receiver_local_owns_user_method_v1`). When
the user type defines it, the fallback is skipped and the already-lowered
receiver is handed to the unresolved arm, so the receiver is not evaluated
twice.

## Evidence

- MIR spec `test/01_unit/compiler/mir/user_method_builtin_name_lowering_spec.spl`,
  run with the Rust seed built from `10a8c7a58c0`: 1 of 6 passed before the
  fix (the builtin control), 6 of 6 after.
- Native fixture `test/fixtures/native_user_method_builtin_name/main.spl`
  with `expected_output.txt` (seed interpreter output, 38 lines). On the
  Stage 2 built from `10a8c7a58c0`, before the fix: cranelift builds with
  rc 0 and the binary dies with SIGSEGV (rc 139) on the first line; llvm
  builds with rc 0, exits 0 and prints 30 of 38 lines wrong (`join=` empty,
  `len=1`, `char_at=` empty, `find=-1`). The 30 lines are exactly the cases
  the MIR table predicts.
- Not yet re-run natively after the fix: that needs a Stage 2 built from this
  source. Re-check with
  `FX_SRC=<src> sh check_fx.sh <stage2> <workdir> umbn=test/fixtures/native_user_method_builtin_name/main.spl`;
  both backends must report `SAME (38 lines)`.
- Five neighbouring MIR specs fail on this base with and without the fix,
  with the same 29 failing examples (`text_builtin_rfind_lowering_spec`,
  `text_search_index_abi_source_spec`, `bare_builtin_method_literal_receiver_spec`,
  `bootstrap_binary_lowering_source_spec`, `option_variant_order_source_spec`).
