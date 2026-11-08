# Seed: untyped `val n = s.byte_len()` holds a raw i64 misdecoded as a tagged value

Severity: P1 (silent wrong values; non-terminating loops). Status: fix-implemented-verification-pending.

Found via PR #7883, which papered over it in `src/compiler/00.common/module_path_naming.spl`
(`# @workaround bug=hir_unit_specs_hang_over_300s_2026-11-06`): an untyped
`val value_len = value.byte_len(); val needle_len = needle.byte_len()` made
`start <= value_len - needle_len` never become false, so the scan loop ran past 300 s.
`src/compiler/bootstrap_admission/stage2_module_path_naming.spl` carries the same pattern.

## Reproduction (deployed seed `bin/simple.exe` of 2026-11-04 16:58, JIT lane, 2026-11-09)

```
fn f(value: text, needle: text):
    val a = value.byte_len()
    val b = needle.byte_len()
    val c: i64 = value.byte_len()
    print("a={a} b={b} c={c} a-b={a - b} c-b={c - b}")
f("semantic_surface.spl", "/")
```

prints `a=<value:0x14> b=nil c=20 a-b=2 c-b=19` — `a` is the raw word 20 shown as an
unknown-tag RuntimeValue, `b` (raw 1) decodes as `nil`, and `a - b` yields 2 (the
`2.0` float the original report saw: a tagged-arithmetic misdecode). Only the
explicitly typed `c` is correct. The tree-walking interpreter path (top-level
statements, no `main`) prints 2 correctly, so the defect is JIT-only.

## Root cause

`src/compiler_rust/compiler/src/hir/lower/expr/mod.rs`, `lower_builtin_method_call`:
`byte_len` was missing from the method result-type tables, so the call was typed
`TypeId::ANY`, MIR emitted no `UnboxInt`/`BoxInt`, and the raw i64 returned by
`rt_string_len` was carried as if it were an already-tagged RuntimeValue. The typed
`val c: i64 = ...` form survived only because the declared type forces an `UnboxInt`
and `rt_value_unbox_int` passes an untagged word through verbatim. Same gap class as
`jit_string_length_var_control_flow_wrong_value_2026-07-17`, `seed_bytes_u8_boxtag_2026-07-17`,
`jit_bool_result_type_gap_2026-07-29`.

## Status of the fix (source audit 2026-11-09, origin/release/1.0.0 @ 88dece8a330)

- **Typed `text` receiver — already fixed on origin, not yet deployed.** PR #7174
  (`177e47d13d9`, merged 2026-11-06) added `"char_count" | "byte_len" => Some(TypeId::I64)`
  to the String-receiver table; `a847b9c9573` (2026-11-04) mapped `byte_len` ->
  `rt_string_len` in both Cranelift tables (`codegen/instr/calls.rs`,
  `codegen/instr/closures_structs.rs`). The deployed seed predates both, which is why
  #7883 (2026-11-08) still hit the hang. `module_path_naming.spl` and
  `stage2_module_path_naming.spl` both take `value: text, needle: text`, so they are
  covered by #7174 once the seed is rebuilt.
- **Erased/untyped receiver — still open, fixed here.** The ANY-receiver text table
  (the one carrying `starts_with`/`rfind`/`index_of`/`len`) had no `byte_len` or
  `char_count`, so `fn f(value): val n = value.byte_len()` was still typed ANY and
  misdecoded exactly as above. This change adds both.
- Sibling audit of raw-i64 text builtins: `byte_at`, `char_code_at`, `ord`,
  `codepoint`, `code_point`, `hash` are already covered for STRING and ANY receivers by
  the fallback in `lookup_method_return_type_inner`
  (`native_char_code_at_tag_shift_2026-07-19`); `len`/`length`/`count`/`index_of`/
  `rfind`/`last_index_of`/`find` are in both tables.

## Tests (cargo, `src/compiler_rust/compiler`)

- `hir/lower/tests/expression_tests.rs::byte_len_and_raw_i64_text_builtins_infer_i64`:
  typed-receiver `byte_len` difference (the #7883 loop-bound shape), `byte_at`,
  `char_code_at`, `ord`, and the erased-receiver `byte_len` (red before this change
  on the `erased` case; green after).
- `tests/compile_and_run.rs::untyped_byte_len_difference_is_integer_under_jit`:
  executes the #7883 scan loop under the JIT and asserts integer results.

## Verification pending

Rebuild and redeploy the seed, then run the #7174 spec
`test/01_unit/lib/text/text_byte_len_jit_boxing_spec.spl` and the two cargo tests on
the deployed binary; then remove the `@workaround` in
`src/compiler/00.common/module_path_naming.spl` (PR #7883) and mirror in
`src/compiler/bootstrap_admission/stage2_module_path_naming.spl`.
