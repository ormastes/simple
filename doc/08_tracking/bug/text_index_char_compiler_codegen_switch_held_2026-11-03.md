# Held Stage 2 / Stage 3 Switch: `text[i]` -> `char` Compiler Codegen (`text_index_char_compiler_codegen_switch_held_2026-11-03`)

- **Bug ID:** `text_index_char_compiler_codegen_switch_held_2026-11-03`
- **Severity:** `P1`
- **Status:** `fix-implemented-verification-pending` (staging, HIR diagnostics, lexer migration, and `MirTypeKind.Char` lowering readiness verified; final `50.mir` `Opaque("str")` -> `Char` switch intentionally held pending Stage 3 completion)
- **Related ADR / Siblings:** `doc/04_architecture/adr/ADR-005-text-index-yields-char.md`, `doc/08_tracking/bug/char_literal_lexer_switch_staged_2026-11-03.md`, `doc/08_tracking/bug/db/text_index_char_int_context_warning_to_error_2026-11-03.sdn`

## Current Implementation Audit (`origin/release/1.0.0`, 2026-11-26)

1. **`30.types` type inference (`src/compiler/30.types/type_infer/inference_expr.spl`):**
   - `CharLit` infers `HirTypeKind.Char` (line 615).
   - Non-slice `text[i]` infers `HirTypeKind.Char` while slice `text[a:b]` infers `HirTypeKind.Str` (lines 822-825).
2. **`20.hir` staged diagnostics (`src/compiler/20.hir/exhaustiveness/`):**
   - `char_int_context.spl` (`W-CHAR-INT-CONTEXT` / `E-CHAR-INT-CONTEXT`, `ci_default_mode() == "warn"`, overrideable via `SIMPLE_CHAR_INT_CONTEXT=error` or `SIMPLE_SAFETY_PROFILE=critical|verified`) catches arithmetic and `.to_i64()`/`.to_int()`/... on `char`/`text[i]` while allowing `.ord()`, `as i64`, `.to_digit()`, `.char_code_at()`, `.byte_at()`, and slicing.
   - `char_condition.spl` (`W-CHAR-CONDITION` / `E-CHAR-CONDITION`, `cc_default_mode() == "warn"`) catches char truthiness (`if c:`, etc.) while allowing explicit comparisons (`c == 'a'`).
3. **`10.frontend` lexer & compiler call sites:**
   - `src/compiler/10.frontend/core/lexer_struct.spl` uses `source_chars: [text]`, slices (`source[start:end]`), and `.byte_at(...)` with zero `[...].to_i64()` sites.
   - `src/compiler/20.hir/` (`hir_definitions.spl`, `hir_forward_lowering.spl`, etc.) uses `for ch in raw` / `rest[ci:ci+1]` with zero `[...].to_i64()` coercions.
   - **Remaining out-of-lane call site flagged for Stage 3 prep:** `src/compiler/10.frontend/core/interpreter/eval_builtins.spl:54,63` (`_eval_parse_i64` still reads `val sign_ch = t[i]` and `val code = t[i].char_code_at(0)`, which should become `t[i:i+1]` / `t.char_code_at(i)` when opening the final switch outside `20.hir`).
4. **`50.mir` frozen-Stage 2 hold (`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`):**
   - `expr_dispatch.spl:4911-4944` preserves `rt_index_get` -> `decode_runtime_value(char_at_local, MirTypeKind.Opaque("str"))` so frozen Stage 2 compiling the compiler lexer does not break prematurely.
   - `expr_dispatch.spl:2278,2291-2302` already maps `MirTypeKind.Char` via `rt_char_from_code` (verified via `c.chr()` -> `rt_char_from_code`).

## Verification Evidence (`2026-11-26`, `BF-8`)

- `test/01_unit/compiler/held_verify/text_index_char_switch_readiness_spec.spl` (`6/6` pass, `--mode=interpreter`)
- `test/01_unit/language/text_index_ruby_semantics_spec.spl` (`13/13` pass, `--mode=interpreter`)
- `test/01_unit/compiler/hir/char_int_context_spec.spl` (`16/16` pass, `--mode=interpreter`)
