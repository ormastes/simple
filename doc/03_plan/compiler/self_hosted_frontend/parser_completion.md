# Parser Completion Plan — Self-Hosted Frontend

**Date:** 2026-06-11  
**Status:** Interim delegation active — `check` and `lint` delegate to `simple_seed` (Rust sibling).  
**Goal:** Remove delegation; stage4 in-process `check src/lib/common/text.spl` and `lint` green in
Docker without delegation, then full `src/lib` sweep at 0 parser errors.

---

## Already Fixed (do not replan)

| Fix | Commits |
|-----|---------|
| `val`/`var` class fields + advance-on-error class-body loop | `dec6a0d97a` |
| `new` keyword as method name | `dec6a0d97a` |
| Trait signature-only method bodies (no body required) | `445daa40f7` |
| Positional-class-match rewrite in `convert_decl_method_fn` | `445daa40f7` + local trait fix |
| OOB array guards | `445daa40f7` |

Open parity bugs (reference only):
- `doc/08_tracking/bug/positional_class_match_wide_destructure_2026-06-11.md`
- `doc/08_tracking/bug/compiled_array_oob_read_segfault_2026-06-11.md`

---

## Gap-Class Table (from 1855-file sweep, 2026-06-11)

All 1855 target files failed. The two error populations:

- **rc=124** (1813 files): parser error stops immediately; no phase-2 start.
- **rc=139** (29 files): crash (SIGSEGV/SIGABRT) during parse.

The line 103:27 `'&'` errors are in files that fail *before* `[BOOTSTRAP-PHASE]` is logged,
meaning `parse_full_frontend` is called on a prelude-closure file (loaded during
`parse_bootstrap_default_file`) that contains the bitwise `&` operator (e.g.,
`src/compiler/00.common/simd_types.spl:375: (n & (n - 1)) == 0`,
`attributes_part2.spl:550`) — these are in the **check prelude closure** and poison
every run that hits them.

| # | Error class | Example file:line | Est. files | Parser area |
|---|-------------|-------------------|------------|-------------|
| G1 | `expected ), got Error '&'` — `&` lexed as Error token | `src/lib/common/audio_effects.spl` (prelude: `simd_types.spl:375`) | **522** | `lexer_struct.spl` — add `&` emit rule (TOK_AMPERSAND=120 defined in `tokens.spl` but lexer silently drops it) |
| G2 | `unexpected token in expression: Indent` — multiline expr continuation | `src/lib/common/animation/spring.spl:30` | **459** | `parser_expr.spl` / `parser_primary.spl` — skip/absorb Indent tokens in expression positions |
| G3 | `unexpected token in expression: ','` — multi-item `use {a,b,c}` or arg list | `src/lib/common/compress/gzip.spl:6` | **147** | `parser_decls_use.spl` / `parser_expr.spl` — allow comma in import list and fn-arg parser |
| G4 | `expected 'pc' before pointcut expression` — `@allow(...)` annotation at line 1:7 treated as AOP pointcut | `src/lib/common/bcrypt/key_derivation.spl:1` | **61** | `aop_predicate_parser.spl` / `parser_decls.spl` — `@attr(...)` annotations must be parsed *before* the AOP `pc{...}` dispatcher is invoked |
| G5 | `expected field name after '.'` — numeric tuple-field access `.0`/`.1` | `src/lib/common/color/manipulate.spl:32` | **60** | `parser_primary.spl` / `parser_expr.spl` — accept integer literal after `.` as tuple index |
| G6 | `expected 'case' in match block` — `match` arm with `Enum.Variant:` indented body | `src/lib/common/llm/content_authority.spl:30` | **57** | `parser_stmts.spl` — accept `Ident.Ident:` as a match arm without the `case` keyword |
| G7 | `expected ), got ','` — trailing/multiple args variant | `src/lib/common/cbor/utilities.spl:15` | **51** | `parser_expr.spl` — overlaps G3; same comma-in-call fix |
| G8 | `expected Ident, got self` — extension `fn f(self: T)` param | `src/lib/common/color/types.spl:9` | **38** | `parser_decls_part1.spl` — allow `self` as first param name in fn signature |
| G9 | `unexpected token in expression: '.'` — chained call / glob re-export `export X.*` | `src/lib/common/json/__init__.spl:1` | **35** | `parser_decls.spl` — parse `export Ident.*` as glob re-export |
| G10 | `expected Ident, got fn` — `fn` inside enum body (method on enum variant) | `src/lib/common/doctest/matcher.spl:12` | **31** | `parser_decls_part2.spl` — allow `fn` declarations inside enum bodies |
| G11 | `expected :, got Newline` — multi-line fn signature (return type on next line) | `src/lib/common/io/traits.spl:112` | **31** | `parser_decls_part1.spl` — allow Newline+Indent after `->` before `:` body start |
| G12 | `unexpected token: '?'` — nullable type `T?` or `?` postfix operator | `src/lib/nogc_sync_mut/io/pipe.spl:91` | **29** | `parser_expr.spl` / `parser_primary.spl` — handle `?` postfix for option unwrap |
| G13 | `expected Ident, got use` — `export use X.{...}` re-export form | `src/lib/common/cert/pem.spl:11` | **26** | `parser_decls.spl` — parse `export use path.{names}` as re-export statement |
| G14 | `expected ), got Ident 'as'` — `as` cast in expression | `src/lib/common/color/lab_xyz.spl:67` | **22** | `parser_expr.spl` — parse `expr as Type` infix cast |
| G15 | `unexpected token in class body` — `static` or other modifier in class | `src/lib/nogc_sync_mut/simd/vector.spl:20` | **18** | `parser_decls_part2.spl` — accept `static` modifier in class member parse |
| G16 | `expected parameter name` — lambda/closure parameter edge | various | **17** | `parser_expr.spl` |
| G17 | `expected Ident, got _` — wildcard `_` as param name | various | **13** | `parser_decls_part1.spl` — accept `_` as valid param name |
| G18 | `unexpected token: Error` (non-`&`) + misc low-count | various | **12** | lexer + parser_expr |

**Total accounted: ~1,629 of 1,855.** Remainder: crashes (rc=139, 29 files) and
minor 1-off patterns (`static`, `loop`, `|`, `>`, `<`, `:` in expression).

---

## Milestone Ordering

Fix in prelude-closure-first order (G1→G4 poison every run through prelude files).

### Verification harness pattern (use for every milestone)

**Protocol corrections (2026-06-11, learned from M1 false-green):**
- `parser_error_count()` is a hardcoded-0 stub (`core/parser.spl:500`) — NEVER use it.
  Use `parser_has_errors() -> bool` and scan output for `[parser_error]` lines.
- `bin/simple check/lint/run` are DELEGATED to the Rust seed since the 2026-06-11
  deploy — they do NOT exercise the lean parser natively. Run harnesses with the
  seed directly: `src/compiler_rust/target/release/simple run tmp/site12/<h>.spl`
  (the seed interprets the lean parser .spl sources, so this DOES test the fix).
- A harness importing only parser+ast segfaults the seed interpreter; adding
  `use compiler.frontend.flat_ast_bridge_part2.{flat_ast_to_module}` as a third
  import avoids it (template: `tmp/site12/m1_reverify.spl`).
- ALWAYS include a must-fail control case (e.g. `"fn h() -> i64:\n    val q = ((\n"`
  → `parser_has_errors()` must be true). If the control passes, the harness is
  broken — stop and investigate.

```
# inline harness (no file_ops import)
use compiler.core.parser.{parse_module, parser_has_errors}
use compiler.core.ast.{ast_reset}
use compiler.frontend.flat_ast_bridge_part2.{flat_ast_to_module}

fn main():
    ast_reset()
    parse_module("<inline source under test>", "case1.spl")
    print "case1 has_errors={parser_has_errors()}"
    ast_reset()
    parse_module("fn h() -> i64:\n    val q = ((\n", "ctrl.spl")
    print "control has_errors={parser_has_errors()}"
```

Run: `timeout 120 src/compiler_rust/target/release/simple run tmp/site12/<h>.spl`

---

### M1 — G1: Lex `&` as TOK_AMPERSAND (fixes ~522 files) — DONE 2026-06-11

Landed in two halves:
- `1ea5249607` — lexer: `core/lexer_struct.spl` emits `&`(120), `^`(122), `~`(123)
  (previously fell through to Unknown 191).
- `0ff597f009` — parser: infix `&`/`^` (and `|` in the main chain) at the
  multiplication level of `core/parser_expr.spl` `parse_multiplication()` +
  `parse_binary_from()`; prefix `~` in `parse_unary()`. The lexer half alone was
  NOT enough — `tok_precedence()` in `core/tokens.spl` is dead code the parser
  never calls; the leveled chain hardcodes operator kinds.

Verified: `a & b`, `(n & (n - 1)) == 0`, `a ^ 3` + `~x` all parse with
`parser_has_errors()=false`; control errors correctly. Regression
`lazy_outline_equivalence_spec` 16/16.
Known follow-up: `|`/`&`/`^` sit at multiplication level, diverging from the
`tok_precedence` spec (pipe 4 < caret 5 < amp 6 < eq 7) — recorded in
`doc/08_tracking/bug/lean_parser_bitwise_pipe_precedence_divergence_2026-06-11.md`.

---

### M2 — G4: `@attr(...)` annotations before AOP pointcut dispatch (fixes ~61 files)

Poisons prelude — `@allow(...)` at line 1:7 dispatches to AOP `pc{...}` parser.  
**File:** `src/compiler/10.frontend/core/parser_decls.spl` (or `parser_decls_part1.spl`)  
When `@` is seen at top-level, parse annotation name+args and attach as attribute before reaching AOP path.  
**Test:** `"@allow(star_import)\nval x = 1"` → 0 errors.  
**Docker:** `bin/simple check src/lib/common/bcrypt/key_derivation.spl`

---

### M3 — G2: Indent tokens in expression continuations (fixes ~459 files)

**Files:** `src/compiler/10.frontend/core/parser_expr.spl`, `parser_primary.spl`  
Skip/absorb `Indent` (and `Newline` at non-statement boundaries) inside infix, call-arg, and struct-literal field loops.  
**Test:** Multi-line `return SomeStruct(\n    field: v,\n    ...)` → 0 errors.  
**Docker:** `bin/simple check src/lib/common/animation/spring.spl`

---

### M4 — G3+G7: Comma in import lists and call args (fixes ~198 files)

**Files:** `src/compiler/10.frontend/core/parser_decls_use.spl`, `parser_expr.spl`  
`use mod.{a, b, c}` — treat `,` as separator in `{...}` import body; same in call-arg parser.  
**Test:** `"use std.foo.{bar, baz}"` and `"val r = f(a, b)"` → 0 errors each.  
**Docker:** `bin/simple check src/lib/common/compress/gzip.spl`

---

### M5 — G8: `self` as first parameter name (fixes ~38 files)

**File:** `src/compiler/10.frontend/core/parser_decls_part1.spl`  
Accept `self` as a valid param name (same handling as `me`).  
**Test:** `"fn to_string(self) -> text: \"x\""` in class body → 0 errors.  
**Docker:** `bin/simple check src/lib/common/color/types.spl`

---

### M6 — G5: Numeric tuple-field access `.0`/`.1` (fixes ~60 files)

**File:** `src/compiler/10.frontend/core/parser_primary.spl`  
After `.`, accept integer literal → `TupleIndex(n)` AST node.  
**Test:** `"val r = pair.0"` → 0 errors.  
**Docker:** `bin/simple check src/lib/common/color/manipulate.spl`

---

### M7 — G6: `match` arms without `case` keyword (fixes ~57 files)

**File:** `src/compiler/10.frontend/core/parser_stmts.spl`  
Accept `Ident.Ident:` or `Ident:` directly as match arm; `case` keyword stays optional.  
**Test:** Enum match arms without `case` → 0 errors.  
**Docker:** `bin/simple check src/lib/common/llm/content_authority.spl`

---

### M8 — G9+G13: `export X.*` and `export use X.{...}` (fixes ~61 files)

**File:** `src/compiler/10.frontend/core/parser_decls.spl`  
After `export`: `use` → re-export; `Ident.*` → glob re-export.  
**Test:** `"export array_ops.*"` and `"export use std.base_encoding.base64.{base64_decode}"` → 0 errors each.  
**Docker:** `bin/simple check src/lib/common/json/__init__.spl`

---

### M9 — G10+G11+G14+G15: Mid-count gaps (fixes ~81 files)

One agent pass across four files:
- **G10** `fn` in enum body → `parser_decls_part2.spl`: allow `fn` inside enum member loop.
- **G11** Newline before `:` after `->` → `parser_decls_part1.spl`: skip Newline+Indent before body `:`.
- **G14** `as` cast → `parser_expr.spl`: parse `expr as Type` infix.
- **G15** `static` in class body → `parser_decls_part2.spl`: accept `static` modifier.

**Docker:** `bin/simple check src/lib/common/doctest/matcher.spl`

---

### M10 — G12+G16+G17+G18: Low-count cleanup (fixes ~71 files)

- `?` postfix (type `T?` and `expr?` unwrap) → `parser_primary.spl`.
- `_` as param name → `parser_decls_part1.spl`.
- `loop` expression → `parser_expr.spl`.
- `|` in pattern position → `parser_stmts.spl`.

---

### M11 — SIGSEGV / rc=139 crashes (29 files)

Reproduce each via inline harness. Cross-reference `compiled_array_oob_read_segfault_2026-06-11.md`.
Fix OOB reads in parser recovery paths: `parser_decls_part3.spl`, `parser_primary_part3.spl`.

---

### M12 — Flat-bridge hardening + remove delegation

**Files:** `src/compiler/10.frontend/flat_ast_bridge_part1.spl`, `flat_ast_bridge_part2.spl`
1. Verify `SIMPLE_BOOTSTRAP_DECL_*` env-var transport covers all new AST node types from M1–M11.
2. Remove `simple_seed` delegation guards from `src/app/cli/check.spl` and lint entry.
3. **Gate:** `docker run --rm simple-stage4 bin/simple check src/lib/common/text.spl` exits 0; full 1855-file sweep reports 0 errors.

---

## Docker re-check command (canonical)

```bash
docker run --rm simple-stage4 \
  bash -c 'bin/simple check src/lib/common/text.spl && echo GATE_PASS'
```

Full sweep (after M12):
```bash
docker run --rm simple-stage4 \
  bash -c 'for f in $(find src/lib -name "*.spl" | sort); do bin/simple check "$f" || echo "FAIL $f"; done | grep FAIL | wc -l'
```
