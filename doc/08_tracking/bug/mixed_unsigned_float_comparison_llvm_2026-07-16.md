# Suffixed numeric literals silently became the integer 3 (root cause of `mixed_unsigned_float_comparison_llvm`)

- status: source fixed 2026-07-16 (both root-cause bugs); verified with real
  native builds (fresh cache, no bootstrap)
- severity: top (silent wrong answer, language-wide — not scoped to
  comparisons, not scoped to this one harness case)
- harness case: `mixed_unsigned_float_comparison_llvm`
  (`scripts/check/check-native-seed-parity.shs`, `run_strict_dual_backend_case`)

## Correction to an earlier hypothesis in this lane

An earlier version of this document (and an earlier patch) claimed the root
cause was in `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl`'s
`translate_binop` (comparison predicate/type picked from the LEFT operand
only, plain `value_as_type` instead of the signed-aware
`value_as_type_signed`). **That was wrong** — a coordinator's real-build
verification showed the patch changed nothing (native output identical with
and without it: `01010000000011111111` either way). Direct A/B testing below
confirms `core_codegen.spl`'s comparison lowering is provably NOT
on this case's hot path: with the two real fixes below in place, the case
passes bit-for-bit whether or not `core_codegen.spl` carries the
`translate_binop` change. That change has been **dropped** (reverted) rather
than shipped unverified. `core_codegen.spl` and
`test/01_unit/compiler/backend/llvm_comparison_operand_type_spec.spl` are
therefore unmodified by this fix.

## Real root cause 1 — `EXPR_SUFFIXED_LIT` unhandled in the flat-AST bridge

`src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl`, function
`convert_flat_expr`, converts the parser's flat-AST node tags into the
tree-shaped `Expr`/`ExprKind` used by everything downstream. It had **no
branch** for tag `EXPR_SUFFIXED_LIT` (=36) — the tag produced for *any*
numeric literal carrying an explicit primitive-type unit suffix: `255u8`,
`65535u16`, `4294967295u32`, `0x8000000000000000u64`, `254.5f32`, ... (bare
literals like `254.5`, `0.0`, `9223372036854775808.0` have no suffix and were
never affected). With no matching `elif`, every suffixed literal fell through
to the function's final catch-all:

```
else:
    return Expr(kind: ExprKind.NilLit, span: span)
```

`HirExprKind.NilLit` lowers in MIR (`expr_dispatch.spl`) to the reserved nil
sentinel `Const(Int(3), i64)` (bug #137/native_i64opt_some0_collapses_to_nil
picked `3` specifically so it can never collide with a real `Some(0)`
payload). So **every suffixed numeric literal in the entire language
silently became the integer constant `3`**, cast down to whatever type
the surrounding context expected — not just in comparisons, not just in this
one harness case.

Fix: added an `EXPR_SUFFIXED_LIT` branch that reads the suffix name
(`expr_get_str`), builds an AST `Type(kind: TypeKind.Named(suf_name, []))`
for it, builds the real literal (`FloatLit` when the suffix starts with `f`,
else `IntLit`, reading the correct flat-AST slot via `expr_get_float`/
`expr_get_int`), and wraps it as `ExprKind.Cast(literal, suf_type)` — the
same mechanism already used for `i32(x)`-style call-syntax casts, which HIR
lowering and MIR building already handle correctly end-to-end.

## Real root cause 2 — hex-literal suffix lexed as empty (separate, pre-existing bug, only exposed once root cause 1 stopped masking it)

Fixing root cause 1 alone still failed to build `0x8000000000000000u64`
specifically (`error: HIR lowering error: internal: failed to extract named
type` — an empty type name). Traced to
`src/compiler/10.frontend/core/lexer_struct.spl`, `CoreLexer.scan_number`'s
hex-literal branch:

```
hex_suffix = self.char_slice(hsuf_start, pos)
core_token_suffix_save(hex_suffix)          # <- saved suffix here...
if hex_suffix != "":
    ...
    self.make_token(7, num_text, start_line, start_col)   # ...then WIPED by this
```

`make_token()` calls `core_token_capture()`, which **unconditionally**
resets `core_last_token_suffix_slot[0] = ""` (a lazy-init side effect, not
gated on token kind). The **decimal**-literal suffix path a few lines below
already saves the suffix *after* calling `make_token()`, specifically to
avoid this reset — but the hex branch saved it *before*, so the correct
suffix ("u64") was immediately overwritten with "" by `make_token`'s own
internal reset. The parser then read an empty suffix name for any hex
literal with a suffix, even though `kind` was still (correctly) 7 — so
`0x10u64`, `0x8000000000000000u64`, etc. all lexed as if unsuffixed, no
matter how root cause 1 was fixed. Confirmed via direct trace: readback of
`core_lexer_last_suffix_get()` was `"u64"` immediately after
`core_token_suffix_save`, and `""` one line later after `make_token()`.
Decimal-suffixed literals (`5u64`, `05u64`) and hex literals without a
suffix (`0x10` as plain `i64`) were both unaffected — only the hex+suffix
combination hit this ordering bug.

Fix: moved `core_token_suffix_save(hex_suffix)` to run *after*
`self.make_token(...)`, matching the already-correct decimal path.

## Hand-computed truth table (ground truth vs. the harness's fixed expected string)

The harness case is `run_strict_dual_backend_case ... "11111111111111110101"`
— a fixed native-authoritative expected string, not a live seed-run oracle.
This was already mathematically correct (verified by hand below); the seed
oracle needed no correction.

| # | expr | truth | # | expr | truth |
|---|------|-------|---|------|-------|
| 1 | `u8v(255) > 254.5f32` | 1 | 11 | `4294967294.5 < u32v(4294967295)` | 1 |
| 2 | `u8v >= 254.5f32` | 1 | 12 | `4294967294.5 <= u32v` | 1 |
| 3 | `254.5f32 < u8v` | 1 | 13 | `u64v(2**63) > 0.0` | 1 |
| 4 | `254.5f32 <= u8v` | 1 | 14 | `u64v >= 0.0` | 1 |
| 5 | `u16v(65535) > 65534.5` | 1 | 15 | `0.0 < u64v` | 1 |
| 6 | `u16v >= 65534.5` | 1 | 16 | `0.0 <= u64v` | 1 |
| 7 | `65534.5 < u16v` | 1 | 17 | `u64v < 2**63 (as f64)` | 0 (equal) |
| 8 | `65534.5 <= u16v` | 1 | 18 | `u64v <= 2**63 (as f64)` | 1 (equal) |
| 9 | `u32v(4294967295) > 4294967294.5` | 1 | 19 | `2**63(f64) > u64v` | 0 (equal) |
| 10 | `u32v >= 4294967294.5` | 1 | 20 | `2**63(f64) >= u64v` | 1 (equal) |

Concatenated: `11111111111111110101` — matches expected exactly.

## Before / after (real native builds, fresh `build/native_cache` each run)

| build | output | matches want |
|---|---|---|
| origin tip (both root causes present) | `01010000000011111111` | no |
| + convert_nodes.spl fix only (root cause 1) | build FAILS on `0x8000000000000000u64` ("failed to extract named type") — loud, not silent | n/a |
| + both fixes (root cause 1 + 2) | `11111111111111110101` | **yes** |
| + both fixes, `core_codegen.spl` reverted to original (A/B control) | `11111111111111110101` | **yes** (proves core_codegen.spl change was unnecessary) |

Isolated per-width probes (separate tiny `.spl` files, one width each) also
match: u8-only `1111`, u16-only `1111`, u32-only `1111`, u64-only `11110101`
— all against hand-computed expected values.

## Files changed

- `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl` — added the
  `EXPR_SUFFIXED_LIT` branch to `convert_flat_expr`.
- `src/compiler/10.frontend/core/lexer_struct.spl` — reordered
  `core_token_suffix_save` to run after `make_token()` in the hex-literal
  branch of `CoreLexer.scan_number`.

No other files are touched by the final patch (the earlier, dropped
`core_codegen.spl` / unit-spec changes are reverted and NOT part of this
diff).

## CONFLICT-FLAGs

None. This patch does not touch
`src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl` (the file a
parallel lane owns for Option.map cast emission) or
`test/01_unit/compiler/backend/llvm_comparison_operand_type_spec.spl` at
all — both are back to their origin-tip state.

## Follow-up (out of scope for this fix, not blocking)

`src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl`'s
`translate_binop` Eq/Ne/Lt/Le/Gt/Ge cases still pick `cmp_ty` from
`get_operand_type(left)` alone and cast both operands with plain
`value_as_type` (not the signed-aware `value_as_type_signed`). In the
current pipeline this is masked for genuinely mixed int/float *ordered*
comparisons by `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`'s
`mixed_numeric_kinds` handling, which promotes both operands to f64 (with
correct signedness via `emit_cast`/`translate_cast_float_signsafe`) before
they ever reach `translate_binop` — confirmed unreachable via three probes
(this harness case, an isolated declared-variable probe, and a function-call
operand probe). It could still be live for constructs where
`local_mir_type_of` can't determine an operand's type up front (e.g. some
array/dict/struct-field-read operand feeding a comparison). Left as a
documented static-analysis finding, not an applied fix, per this lane's
"never ship an unverified change" rule.
