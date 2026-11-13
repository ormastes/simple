# Pure-Simple lowering cuts `s[a:b]`, `s[a..b]` and `s[i]` on text by bytes

**Status:** FIXED (2026-11-13, branch `work/stage3-index-slice-codepoint-20261113`)
**Area:** frontend bridge / MIR lowering (text)

## Symptom

Owner decision 2026-11-13: `len()`, `s[i]`, `s[a:b]` are code points;
`substring` / `slice` / `index_of` are bytes. The seed lowers `x[a:b]` to
`rt_slice` (code points). The pure-Simple lowering that Stage 2 uses to build
Stage 3 cut them by bytes. A program built by Stage 2 with
`s = "—xy"` printed byte 128 (the em dash's second byte) for `s[1:2]`,
`s[1..2]` and `s[1]`, and `\x80\x94xy` for `s[1:]`.

## Root cause

- `convert_nodes.spl` (EXPR_SLICE) rewrote `s[a:b]` as `MethodCall(s, "slice")`,
  so MIR could not tell it from a written `.slice(a, b)`, and both text arms in
  `lower_method_call` sent it to the byte cutter `spl_str_slice`.
- `try_lower_text_range_index` (`text_index_ranges.spl`) sent `s[a..b]` to
  `spl_str_slice`.
- `s[i]` (`expr_dispatch.spl`) bounds-checked in code points but called
  `rt_string_char_at`, which the C runtime keeps byte-indexed.

## Fix

The bridge keeps the method name `slice` for `x[a:b]` and sets
`Expr.bracket_slice`. HIR lowering copies it to `HirExpr.bracket_slice`
(persisted by the generated HIR codec; codec v18 / canonical v8 reject older
frames). Every HirExpr rebuild that copies an existing `kind` (resolver, block
tail, typed receiver, union rewrite, native-trait payload) carries the flag.
`lower_method_call` takes `bracket_slice` and, for a text receiver only, calls
`lower_text_codepoint_slice_v1` (`rt_slice`, tagged receiver, open end
`i64::MAX`, matching the seed's `lower_slice`). Resolution, typing and user
classes with `fn slice` behave exactly as for `.slice`; a written
`.slice`/`.substring` stays a byte cut. Range indexes on text use the same
helper. `s[i]` calls `rt_index_get`, whose text path now has an ASCII fast path
(memoized flag) in both runtimes and uses the cached code-point count otherwise.

A first attempt spelled the bracket form as a method named `__index_slice`.
Review rejected it: it changed dispatch for user classes and the strict
resolver reported `no method '__index_slice'` for `v[1:3]` on any class with
`fn slice`. The spec pins all three cases.

Spec: `test/01_unit/compiler/mir/text_bracket_slice_codepoint_lowering_spec.spl`.
