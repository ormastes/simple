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

### M2 — G4: `@attr(...)` annotations before AOP pointcut dispatch (fixes ~61 files) — DONE 2026-06-11

Landed in `03a0aaaeda` (local line) / grafted to origin. Dispatch site was
`core/parser_decls_part2.spl:313` (`elif par_kind_get() == 171:` in
`parse_module_body()`). Two root causes:
1. The decorator-name capture only accepted ident (kind 6); `allow` lexes as
   keyword kind 218, so the name stayed empty, `(star_import)` was left
   unconsumed, and the loop re-dispatched `allow` to `parse_arch_rule_decl` →
   AOP pointcut error at 1:7. Fixed: accept non-newline keyword kinds as
   annotation names.
2. Unknown decorators (not gpu/simd/packed/derive) had no else branch. Fixed:
   consume-and-continue so the following declaration parses normally.

Verified: `@allow(star_import)\nval x = 1`, `@allow(unused)` before fn, stacked
`@inline\n@allow(unused)` all parse with `parser_has_errors()=false`; control
errors correctly; lazy_outline_equivalence 16/16.

---

### M3 — G2: Indent tokens in expression continuations (fixes ~459 files) — DONE 2026-06-11

Landed in `9b95620a44` (local line) / grafted to origin. Approach (a): LEXER-level
suppression, not the parser-level skip loops originally sketched here. The lexer
(`core/lexer_struct.spl`) already suppressed Newline(180) inside parens; the gap
was `handle_indentation()` emitting Indent(181)/Dedent(182) regardless of
`paren_depth`. Fix: 4-line guard (lines ~493-527) — when `paren_depth > 0`, skip
the indent-stack comparison and scan the next token directly; the indent stack is
left untouched so block structure resumes correctly after the closing bracket.

Verified: multiline call args, multiline struct literal (spring.spl form),
parenthesized infix continuation all parse with `parser_has_errors()=false`;
M1/M2 cases stay green; unclosed-paren control still errors;
lazy_outline_equivalence 16/16. Import lists `use std.x.{aa,\n  bb}` still fail
— that is G3 comma handling in `parser_decls_use.spl` (M4), not layout tokens.

---

### M4 — G3+G7: Comma in import lists and call args (fixes ~198 files) — ALREADY GREEN 2026-06-12

No parser change was needed. Investigation (2026-06-12) found:
- The import-list loop in `parser_decls_use.spl:92-121` already consumes `,`(160)
  and breaks on `}`(143)/`)`(141); the lexer's `paren_depth` already covers
  `{`/`}` (`lexer_struct.spl:768-776`), so multiline `{...}` bodies suppress
  Indent/Dedent post-M3. Call-arg commas were also already handled.
- The earlier observed failure was a HARNESS BUG: Simple string literals
  interpolate `{...}`, so `"use std.x.{aa,\n  bb}"` was mangled at runtime
  before reaching parse_module. The original G3/G7 sweep counts (147+51 files)
  likely came from REAL errors with a different root cause now fixed by M1-M3,
  or from the same prelude poisoning — re-sweep will tell.

**Harness protocol addition:** sources containing `{`/`}` must be built by
concatenation (`val lb = "{"` … `"use std.x." + lb + "aa, bb" + rb`), never as
direct literals. Template: `tmp/site12/m4_reverify.spl`.

Verified (concat harness): single-line + multiline import lists, `g(1, 2, 3)`
call args, struct-literal guard all `parser_has_errors()=false`; control TRUE;
lazy_outline_equivalence 16/16.

---

### M5 — G8: `self` as first parameter name (fixes ~38 files)

**File:** `src/compiler/10.frontend/core/parser_decls_part1.spl`  
Accept `self` as a valid param name (same handling as `me`).  
**Test:** `"fn to_string(self) -> text: \"x\""` in class body → 0 errors.  
**Docker:** `bin/simple check src/lib/common/color/types.spl`

---

### M6 — G5: Numeric tuple-field access `.0`/`.1` (fixes ~60 files) — DONE 2026-06-12

Landed in `bee9f5f324a` (local line) / grafted to origin. Findings:
- `pair.0` lexes as Ident + `.`(164) + IntLit(1, "0") — the float-lex path only
  fires inside `scan_number()`, so no lexer change was needed.
- No `TupleIndex` AST node (the note above was aspirational): the fix reuses
  `expr_field_access(base, "0", 0)` — the integer text becomes the field-name
  string and flows through the existing flat_ast bridge unchanged.
- Two guard blocks in `core/parser_expr.spl` (`parse_postfix_on` ~689 and
  `parse_postfix` ~825): accept IntLit(1) after `.` before the Ident expect.

Verified: `t.0 + t.1`, chained `t.0.abs()`, float-literal guard `0.5`, M5
spot-check all `parser_has_errors()=false`; control TRUE;
lazy_outline_equivalence 16/16.

---

### M7 — G6: `match` arms without `case` keyword (fixes ~57 files) — DONE 2026-06-12

Landed in `79ce94d8009` (local line) / grafted to origin. Fix site:
`core/parser_stmts.spl:574-576` — the match-arm loop's else branch was an
error-and-advance stub; replaced with a caseless-arm path mirroring the `case`
branch (parse_expr pattern, optional `if` guard, optional `as` binding,
expect `:`, parse_block body, same `arm_new_with_binding_and_rationale` +
`normalize_wildcard_pattern` helpers — no forked pattern parser).

Real arm forms covered: `Enum.Variant:` (content_authority.spl), `Ok(v):` /
`Err(m):` constructor bindings (capability_policy.spl), literal/wildcard
`0:` / `_:`. `case` keyword stays working.

Verified: caseless enum arms, `case` regression, constructor-binding arms,
M6 spot-check all `parser_has_errors()=false`; control TRUE;
lazy_outline_equivalence 16/16.

---

### M8 — G9+G13: `export X.*` and `export use X.{...}` (fixes ~61 files)

**File:** `src/compiler/10.frontend/core/parser_decls.spl`  
After `export`: `use` → re-export; `Ident.*` → glob re-export.  
**Test:** `"export array_ops.*"` and `"export use std.base_encoding.base64.{base64_decode}"` → 0 errors each.  
**Docker:** `bin/simple check src/lib/common/json/__init__.spl`

---

### M9 — G10+G11+G14+G15: Mid-count gaps (fixes ~81 files) — DONE 2026-06-12

Landed in `adc8dcad379` (local line) / grafted to origin. Real-file grounding
shifted two diagnoses:
- **G14** `as` was never a keyword AT ALL — added `TOK_KW_AS = 221` to
  `core/tokens.spl` keyword_lookup; cast loops in `parse_unary()` +
  `parse_binary_from()` (parser_expr.spl) via `expr_cast`; all former
  text-based `as` checks (use-alias in parser_decls_use.spl, newunit in
  parser_decls_part2.spl, match-arm binding in parser_stmts.spl) switched to
  kind 221 — text comparison is UNRELIABLE for in-memory sources because
  `par_text_get()` returns "" when the env-var source transport has a fake path.
- **G15**'s real form (vector.spl:20) was `pass_dn` placeholder in trait/class
  bodies, not `static`; handled `pass/pass_dn/pass_todo/pass_do_nothing` before
  member dispatch (parser_decls_part1.spl).
- **G10** enum `fn/static/me` members → impl-block creation in
  `parse_enum_decl` (parser_decls_part2.spl).
- **G11** Newline+Indent skip after `-> Type` in `parse_fn_decl`
  (parser_decls_part1.spl) and `parse_class_body_method` (parser_decls_use.spl).

Verified (orchestrator harness): enum-fn, trait signature-only methods,
`r as f64` cast, `use std.color as c` alias, `pass_dn` trait body, M6/M8 spot
checks all `parser_has_errors()=false`; control TRUE; lazy_outline_equivalence
16/16 (re-run by orchestrator due to keyword-table blast radius).

---

### M10 — G12+G16+G17+G18: Low-count cleanup (fixes ~71 files) — DONE 2026-06-12

Landed in `2c62bd472c7` (local line) / grafted to origin.
- **G12** `?`(130) postfix in `parse_postfix_on` (~777) + `parse_postfix` (~919),
  parser_expr.spl — covers `expr?` (pipe.spl:91) and `T?` types.
- **G17** `_`(kind 169) accepted in `parser_expect_param_name()`
  (parser_decls_part1.spl:82-91) — no real `fn(_:` uses found in src/lib but
  the helper now matches the Rust seed.
- **G16** inline fn-lambda `fn(s: text) -> i64: body` (string_bench.spl:55,
  replay_driver.spl:75) — `fn`(20) handler at end of `parse_primary_expr`,
  parser_primary_part2.spl.
- **G18** `loop:`(51) handler in the same site (gzip/compression files).

DEFERRED: `|` in pattern position (needs pattern-parser changes — fold into
M11/M12 if the sweep still shows it); no-colon `loop` form (not found in real
files).

Verified (orchestrator harness): `i64?` type + return, `g()?`, `_` param,
inline fn-lambda, `loop:`, M9 as-cast spot check all
`parser_has_errors()=false`; control TRUE; lazy_outline_equivalence 16/16.

---

### M11a — G19: `if val` / `elif val` / `while val` pattern binding — DONE 2026-06-12

NEW gap found by the first post-M10 in-process smoke (masked by prelude
poisoning in the original sweep): the binding forms didn't parse at all,
poisoning the check prelude at src/app/mcp/main_lazy_assistant.spl:701.
Landed in `fff9f3b8559` (local) / grafted to origin. Encoding: parser-level
desugar in `core/parser_stmts.spl` (no AST/bridge changes) —
`if val N = E:` → `STMT_BLOCK([val N = E, if N != nil: …])`;
`while val N = E:` → `while true: { val N = E; if N == nil: break; … }`;
`elif val` covered by recursion. Verified: if/elif/while-val + plain-if
regression green, control TRUE, lazy_outline 16/16.
Note: the flat_ast bridge OOBs on ANY fn in the in-memory harness context
(plain `if` too) — pre-existing harness artifact, not the desugar; real
check-path bridging validated via the docker in-process smoke instead.

### M11b — G21: octal/hex/unicode string escapes + NUL-safe token bridge — DONE 2026-06-12

Found by the post-G19 in-process smoke (check now progresses deep into
src/app). Two issues:
1. **NOT a parser gap — broken file:** `src/app/sdn/commands.spl` opened with
   a lone-`#` block-comment header (invalid grammar — the SEED rejects it too,
   E0002 at 5:1) plus a fused line `use app.ioimport std.process`. Repaired
   the file (normal `#` line comments + split imports); seed check green.
   Lone-`#` headers remain only in `src/compiler_rust/lib/std/src/sdn/*` (seed
   lib, out of owned scope).
2. **G21 lexer gap:** string scanner decoded `\033` as NUL+"33" (`\0` branch
   ate the digit), then `rt_env_set("SIMPLE_BOOTSTRAP_CORE_TOKEN_TEXT", …)`
   ABORTED the whole check (Rust env NUL panic) — the `result.contains(nul)`
   guard provably fails on NUL-bearing text (C-string truncation). Fix in
   `core/lexer_struct.spl`: full `\NNN` octal, `\xNN` hex, `\u{…}` unicode
   decoding (seed parity probed: `"\033"`.len==1, `"\77"`==1, `"\x1b"`==1,
   `"\u{1F600}"` ok) + `has_nul` flag replaces the broken contains() guard.
   ~10 src files use `\033` (cli/formatting, tui/style, tui/terminal, …).
   Verified: tmp/site12/g21_reverify.spl — all 4 escape forms green, control
   TRUE, no abort.

### M11c — G22+G23: keyword path segments + `val _` discard binding — DONE 2026-06-12

Found by the post-M11b in-process check (1153 errors, rc=124 timeout):
- **G22:** `use app.cli.…` / `import app.cli` failed — `cli` is TOK_KW_CLI(212),
  and use-path segments only accepted Ident(6). Fix in `parser_decls_use.spl`:
  `use_kw_segment_text(kind)` helper — a kind is a textual keyword iff
  `keyword_lookup(tok_kind_name(kind)) == kind` (kind-based, so it works for
  in-memory sources where par_text_get() is ""). Applied at first-segment,
  loop-segment, and import-list-name sites. Generalizes the M2 (`allow`) and
  M9 (`as`) keyword-as-identifier pattern to ALL keywords in path positions.
- **G23:** `val _ = expr` / `var _ = expr` discard bindings failed
  ("expected =, got _") — `_` is kind 169. Fix in `parser_stmts.spl`
  parse_val_decl_stmt + parse_var_decl_stmt, same accept-169 pattern as M10
  params.
Verified: tmp/site12/m11c_probe.spl all green + control TRUE; full regression
battery (m5/m8/m9/m10/g19/g21 harnesses) green.

### M11 — SIGSEGV / rc=139 crashes (29 files) — IN PROGRESS 2026-06-12 (re-sweep first)

Approach revised: the 29 crash files' first-error signatures in the 2026-06-11
sweep log (caseless match, `?` in types, Indent continuations, fn-in-enum,
class-body) are all error classes FIXED by M5–M10 — the SIGSEGVs were in
error-recovery paths that should no longer be reached. Instead of chasing
stale crashes: rebuild stage4 with M1–M10, re-run the full src/lib sweep
(`/tmp/s4_resweep.sh`, docker, `SIMPLE_FRONTEND_DELEGATED=1` to force the
in-process lean frontend), then fix only crashes that REMAIN.
Cross-reference `compiled_array_oob_read_segfault_2026-06-11.md` for any
survivors; recovery-path OOB suspects: `parser_decls_part3.spl`,
`parser_primary_part3.spl`.

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
