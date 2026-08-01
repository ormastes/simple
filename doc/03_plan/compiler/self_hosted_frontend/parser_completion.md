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
| G8 | `expected Ident, got self` — extension `fn f(self: T)` param | `src/lib/common/color/types.spl:9` | **38** | `_ParserDecls/fn_struct_decls.spl` — allow `self` as first param name in fn signature |
| G9 | `unexpected token in expression: '.'` — chained call / glob re-export `export X.*` | `src/lib/common/json/__init__.spl:1` | **35** | `parser_decls.spl` — parse `export Ident.*` as glob re-export |
| G10 | `expected Ident, got fn` — `fn` inside enum body (method on enum variant) | `src/lib/common/doctest/matcher.spl:12` | **31** | `_ParserDecls/enum_module_body.spl` — allow `fn` declarations inside enum bodies |
| G11 | `expected :, got Newline` — multi-line fn signature (return type on next line) | `src/lib/common/io/traits.spl:112` | **31** | `_ParserDecls/fn_struct_decls.spl` — allow Newline+Indent after `->` before `:` body start |
| G12 | `unexpected token: '?'` — nullable type `T?` or `?` postfix operator | `src/lib/nogc_sync_mut/io/pipe.spl:91` | **29** | `parser_expr.spl` / `parser_primary.spl` — handle `?` postfix for option unwrap |
| G13 | `expected Ident, got use` — `export use X.{...}` re-export form | `src/lib/common/cert/pem.spl:11` | **26** | `parser_decls.spl` — parse `export use path.{names}` as re-export statement |
| G14 | `expected ), got Ident 'as'` — `as` cast in expression | `src/lib/common/color/lab_xyz.spl:67` | **22** | `parser_expr.spl` — parse `expr as Type` infix cast |
| G15 | `unexpected token in class body` — `static` or other modifier in class | `src/lib/nogc_sync_mut/simd/vector.spl:20` | **18** | `_ParserDecls/enum_module_body.spl` — accept `static` modifier in class member parse |
| G16 | `expected parameter name` — lambda/closure parameter edge | various | **17** | `parser_expr.spl` |
| G17 | `expected Ident, got _` — wildcard `_` as param name | various | **13** | `_ParserDecls/fn_struct_decls.spl` — accept `_` as valid param name |
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
  `use compiler.frontend._FlatAstBridge.module_assembly.{flat_ast_to_module}` as a third
  import avoids it (template: `tmp/site12/m1_reverify.spl`).
- ALWAYS include a must-fail control case (e.g. `"fn h() -> i64:\n    val q = ((\n"`
  → `parser_has_errors()` must be true). If the control passes, the harness is
  broken — stop and investigate.

```
# inline harness (no file_ops import)
use compiler.core.parser.{parse_module, parser_has_errors}
use compiler.core.ast.{ast_reset}
use compiler.frontend._FlatAstBridge.module_assembly.{flat_ast_to_module}

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
`core/_ParserDecls/enum_module_body.spl:313` (`elif par_kind_get() == 171:` in
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

**File:** `src/compiler/10.frontend/core/_ParserDecls/fn_struct_decls.spl`  
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
  _ParserDecls/enum_module_body.spl, match-arm binding in parser_stmts.spl) switched to
  kind 221 — text comparison is UNRELIABLE for in-memory sources because
  `par_text_get()` returns "" when the env-var source transport has a fake path.
- **G15**'s real form (vector.spl:20) was `pass_dn` placeholder in trait/class
  bodies, not `static`; handled `pass/pass_dn/pass_todo/pass_do_nothing` before
  member dispatch (_ParserDecls/fn_struct_decls.spl).
- **G10** enum `fn/static/me` members → impl-block creation in
  `parse_enum_decl` (_ParserDecls/enum_module_body.spl).
- **G11** Newline+Indent skip after `-> Type` in `parse_fn_decl`
  (_ParserDecls/fn_struct_decls.spl) and `parse_class_body_method` (parser_decls_use.spl).

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
  (_ParserDecls/fn_struct_decls.spl:82-91) — no real `fn(_:` uses found in src/lib but
  the helper now matches the Rust seed.
- **G16** inline fn-lambda `fn(s: text) -> i64: body` (string_bench.spl:55,
  replay_driver.spl:75) — `fn`(20) handler at end of `parse_primary_expr`,
  _ParserPrimary/primary_expr.spl.
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

### M11d — G24: `<<`/`>>` shift operators in parse_comparison — DONE 2026-06-12

Found by the host-side pre-sweep harness (tmp/site12/lean_parse_sweep.spl —
parses all src/lib files through the lean parser via the seed interpreter, no
rebuild needed). `(n >> (pos * 8)) & 0xff` failed in src/lib/bitwise_utils.spl:
the lexer splits `<<`/`>>` into two 82/83 tokens (for generics), and the
duplicate comparison chain at parser_expr.spl:433 (parse_binary_from) pairs
them back into shifts but the ACTIVE chain parse_comparison (:227) did not.
Fix: mirrored the two-token pairing into parse_comparison. Verified:
tmp/site12/g24_probe.spl — shr/shl green, nested generics unbroken, control
TRUE.
WATCH (M12): shifts are encoded as expr_binary(82/83) — same op codes as
`<`/`>` — and _FlatAstBridge/convert_nodes.spl:247 flattens ALL binary ops to
BinOp.Add anyway. Op fidelity is part of M12 flat-bridge hardening.

### M11e — G25–G31: keyword members, trailing-op continuation, match arrows, tuples — DONE 2026-06-12

Batch from the 40-min docker check on the M11c binary (855 errors, 14 prelude
files) — all seven verified as lean-only failures (seed compiles these files
daily), fixed by Sonnet agent (local commit 026ea542ad4), orchestrator
round-2 verified via tmp/site12/m11e_probe.spl + full battery:
- **G25** `.new`/keyword member names after `.` (parse_postfix sites)
- **G26** keywords as binding names (`val after = …`) + expr-primary ident
  fallback rescue before the final error branch
- **G27** trailing-binary-operator line continuation (lexer newline
  suppression when last token is binop/comma)
- **G28** match arrow arms `pattern => expr` (kind 168)
- **G29** tuple literals `( a, b, … )` in paren-expr (expr_tuple)
- **G30** `_` elements in tuple destructure
- **G31** tuple assignment `(a, b) = expr` — free via G29 + expr_assign path
Also recorded: doc/08_tracking/bug/interp_state_corruption_parse_module_2026-06-12.md
(P2 seed-interpreter bug — for-in frames and pre-parse fs writes corrupt the
interpreted parser's hex-literal conversion; sweep harnesses use index-while +
no interleaved writes + straight-line generated chunks as workarounds).

### M11 — SIGSEGV / rc=139 crashes (29 files) — IN PROGRESS 2026-06-12 (re-sweep first)

Approach revised: the 29 crash files' first-error signatures in the 2026-06-11
sweep log (caseless match, `?` in types, Indent continuations, fn-in-enum,
class-body) are all error classes FIXED by M5–M10 — the SIGSEGVs were in
error-recovery paths that should no longer be reached. Instead of chasing
stale crashes: rebuild stage4 with M1–M10, re-run the full src/lib sweep
(`/tmp/s4_resweep.sh`, docker, `SIMPLE_FRONTEND_DELEGATED=1` to force the
in-process lean frontend), then fix only crashes that REMAIN.
Cross-reference `compiled_array_oob_read_segfault_2026-06-11.md` for any
survivors; recovery-path OOB suspects: `_ParserDecls/bitfield_aop_arch_decls.spl`,
`_ParserPrimary/asm_match_suffix.spl`.

---

### M11f — G32 `&&`/`||` + G33 `match` as identifier — DONE 2026-06-12

Mined from the first 2h sweep attempt (timed out; buffered BAD lines lost, but
`[parser_error]` leak pinpointed `src/lib/blink/css_parser/selector.spl`).
Sweep infra reworked: chunked driver (/tmp/sweep_driver.sh, 500 files/seed
process — allocate-and-leak runtime balloons a single 6k-file process),
incremental per-file result writes survive timeouts.

- **G32** `&&`/`||`: no fused token existed — lexer emitted two single
  `&`(120)/`|`(121); first consumed as bitwise infix, second errored in
  expression position. Fix in `lexer_struct.spl` scan: `&&`→kind 55 (same as
  keyword `and`), `||`→kind 56 (`or`), checked after `|>`(175). Parser
  precedence comes free via existing parse_and/parse_or.
- **G33** `match` as identifier (`var match = true; match = false; if match:`):
  stmt dispatcher + expr primary dispatched kind 43 straight to
  parse_match_stmt. Fix: split `parse_match_stmt` → advance +
  `parse_match_stmt_tail`; new `g33_kw_ident_follow(kind)` (parser_stmts.spl)
  = "kinds that cannot start an expression" (assign ops 100–106, closers,
  newline/indent/dedent, binops). Both sites consume `match` then route:
  ident-follow → `expr_ident("match")` (+ assignment/compound handling at
  stmt level via parse_postfix_on/parse_binary_from continuation); else →
  match-stmt tail. Tradeoff: `match (x):` / `match -x:` scrutinees still
  parse as match (kinds 140/61 can start expressions).
- Probes: tmp/site12/g32_probe.spl (5 cases), g33_probe.spl (6 cases incl.
  real match-stmt + match-expr + compound assign), g32_file_probe.spl
  (selector.spl end-to-end), m11e/m12a batteries for regression.

### M11g — next gap wave (from rebuilt-stage4 docker check, 855→510 errors) — IN PROGRESS 2026-06-12

Rebuild with M11d/e/f+M12a cut the in-process check from 855 to 510 parser
errors, but NEW blocker: SIGSEGV (rc=139) in flat-bridge on
`src/app/debug/remote/feature/features.spl` (solo-reproducible, 63 errors then
crash; M11c binary did not crash — recovery now produces partial-AST shapes
the bridge reads unguarded; same class as compiled_array_oob_read_segfault
bug doc; interpreted twin = "index 0 but length 0" at bridge entry, verified
truly pre-existing with BOTH pre-M12a parser+bridge swapped in).
**Bridge-OOB FIXED 2026-06-12**: root cause `decl_get_name(idx)` fell through
to the legacy `decl_name[idx]` array which is never populated on the env-var
decl path — empty-array OOB. Fix: bounds guards on 9 `decl_get_*` accessors
in `core/ast_part1.spl` (span/name/ret_type/fields/field_types/
field_defaults/field_bits/type_params/type_param_constraints) + 2 bridge
guards (`STMT_ASSIGN` body[0], `EXPR_DICT_COMP` args) in
`_FlatAstBridge/convert_nodes.spl`. Verified: interpreted m12a_probe now prints
bridge-ok (OOB gone); m11e 8/8 + g33 batteries clean; REBUILT stage4 docker
solo check on features.spl: rc=139 segv ELIMINATED (now runs the whole
prelude closure; rc=124 at 900s with 2,413 errors accumulated across prelude
files = the G34/G35 wave, not a crash).

Gap classes mined from check_m11f.log + solo log:
- **G34** `::` path separator — DONE 2026-06-12: lexer fuses `::` →
  TOK_COLON_COLON (162, pre-existing kind) at lexer_struct.spl:867-874;
  parse_postfix/parse_postfix_on accept 162 alongside 164 (parser_expr.spl
  :681/:826). features.spl 63→0 errors in docker gate.
- **G35** dotted type names in annotations — DONE 2026-06-12:
  parser_parse_type (core/parser.spl:285-298) absorbs `.`/`::` + ident or
  keyword segments (G25 round-trip) into the type name; param/return/val
  positions + generics-after-path probed green. Round-2 verified: g34 4/4,
  g35 5/5, batteries m11e 8/8 g33 5/5 g32 4/4 m12a 5+bridge-ok.
- **G36** raw string literals `r"..."` — DONE 2026-06-12 (agent died
  mid-report; orchestrator verified+grafted `be70b6e954f`): lexer r-prefix
  raw scan in lexer_struct.spl. g36_probe 7/7; all 7 batteries green;
  docker: main_lazy_json.spl 307-class → 0.
- **G37** — NOT a real gap: match-expr-as-initializer and caseless string
  arms parse clean in isolation (g37_probe 5/5); the ':' class was cascade
  fallout from lexical breaks earlier in the files. Lesson: re-mine residue
  after each lexer fix.
- **G38** — DONE 2026-06-12, three real root causes (initial probes
  false-greened because `{...}` interpolates in probe literals — rebuilt
  with pure concat):
  1. Nested string literals inside `{...}` interpolation segments
     (render_adapter.spl:168/170): lean scan_string terminated at the first
     inner quote. Fix: interpolation-aware `{` branch with brace-depth +
     nested-string + escape tracking, seed scan_fstring_impl parity
     (lexer_struct.spl ~:449; `{`+quote → literal, no `}` before EOL →
     literal).
  2. String-literal index `m["k"]`: `bracket_expr_is_invalid` flagged tag-3
     exprs in COMPILED stage4 only — imported EXPR_* const comparisons
     misevaluate compiled (interpreted/compiled divergence; traced with
     SIMPLE_TRACE_EXPR_TAGS). Mitigation: numeric tags in
     parser_expr.spl:80. Divergence recorded as
     doc/08_tracking/bug/stage4_imported_const_compare_2026-06-12.md.
  3. `val` keyword as for-tuple binding name (commands.spl:252
     `for (key, val) in obj.items():`) — parser_stmts.spl:536, generalized
     to full keyword round-trip.
  Docker gate: commands.spl 8→0, main_lazy_json 307→0, render_adapter
  10→0; whole-run totals 2,130 → 20-39. Batteries all green.

ALSO: interpreted parse_module is superlinear in file size AND degrades per
call (selector.spl prefixes: 20→<1s, 40→2s, 80→6s, 160→256s; identical
40-line source parsed twice in one process: 69s then 124s — heap aging).
A/B probe cleared G32: `and`/`&&`/`&`/`||` conditions all within the aging
trend. "Hangs" in sweeps were timeouts, not loops. Interpreted host
pre-sweep retired; compiled stage4 docker check is the loop gate now.
Recorded as doc/08_tracking/bug/interp_parse_superlinear_2026-06-12.md.

#### G41 — long arg lists + enum commas + fn-body use — DONE 2026-06-13
Combined work of two agents + orchestrator, round-2 verified:
- `parser_expr.spl`: call-arg loops `0..100` → `0..10000` with `)`-break
  guards; keyword-as-named-arg-name fallthrough (keyword parses to
  EXPR_IDENT, `:` follows → consume and parse value). Orchestrator
  hardened the new tag compares to numeric literals (6/11) per the P1
  stage4_imported_const_compare bug; same for extract_dotted_path.
- `_ParserDecls/fn_struct_decls.spl`: keyword accepted as parameter name
  (`cli`, `mcp`, `type`, ...) via keyword_lookup round-trip; `_` (169)
  accepted in binding positions (also _ParserPrimary/primary_expr.spl).
- `_ParserDecls/enum_module_body.spl`: enum body skips same-line variant commas,
  advance-on-error recovery (kills the 999× repeat artifact),
  trailing-comma skip.
- `parser_stmts.spl`: `use` inside fn bodies consumed via
  parse_use_stmt_inline → no-op pass stmt (avoids circular import with
  parser_decls_use; parser-level only — import semantics dropped, fine
  for check-parsing).
Round-2 (orchestrator, tmp/site12/g41_iso2.spl + g41_named_only.spl):
named_args_120 false, positional_args_110 false, enum_comma false,
enum_multiline_comma false, control must-fail true.
Docker gate (first pass, tmp/site12/solo_g41b.log):
wm_quality_contract closure 2,340 → 189 errors, max repeat 2× (no
recovery loops). Next gap classes from residue: keyword named-args
edge (cli:/mcp:), `expected :, got if` (25×), `if..then` expr (18×),
dict literals (11×), class-body tokens (7×).

### M12 — Flat-bridge hardening + remove delegation

**Files:** `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl`, `_FlatAstBridge/module_assembly.spl`

#### M12a — binary-op fidelity — DONE 2026-06-12
Resolves the M11d WATCH item. Two halves, landed together:
- `parser_expr.spl`: shift paths now emit `expr_binary(66/67, ...)`
  (TOK_SHL/TOK_SHR — kinds the lexer never produces, free for AST use)
  instead of reusing 82/83; single `<`/`>` comparisons keep 82/83.
  Sites: parse_comparison :233/:243, parse_binary_from :450/:459.
- `_FlatAstBridge/convert_nodes.spl`: new `op_kind_to_binop(kind)` (:208–228) maps
  all 19 binary token kinds to real BinOp variants (Shl/Shr/BitAnd/BitOr/
  BitXor confirmed variant names); replaces the hardcoded `BinOp.Add`
  flattening at :269 (was :247).
- Verified (orchestrator round-2): tmp/site12/m12a_probe.spl — shl/shr/
  lt/generics/comparison-chain all clean, must-fail control true;
  m11e_probe.spl battery unchanged.
- KNOWN PRE-EXISTING (verified by swapping origin bridge file back in,
  identical crash): interpreted `flat_ast_to_module` dies with
  "array index out of bounds: index 0, length 0" right after entry —
  affects seed-interpreted bridge only; compiled stage4 check pipeline
  exercises the bridge fine. Track under M12 remaining work.

#### G42 — `if cond then X else Y` ternary expression — PARSER DONE 2026-06-13
- `parser_stmts.spl parse_if_expr` (:894): after the cond, if the next token
  is Ident(6), consume it (it can only be `then` — block form always has `:`
  there), parse then-expr, optionally consume `else` (kw 41) + parse else-expr,
  return `expr_if_expr(cond, then, else, 0)` with all three branches
  faithfully populated. Block form (`:`) unchanged.
- PITFALL (cost a debug cycle): detect `then` on KIND alone, not text.
  `par_text_get()` returns "" for this token under the interpreter (offset-
  based retrieval per interp_parse_superlinear bug), so a `== "then"` check
  silently never fires in probes — even though compiled stage4 shows the text.
- Round-2 (orchestrator, tmp/site12/g42_probe.spl): ifthen_val / ifthen_arg /
  ifthen_calls → false; dict cases stay false; control must-fail true.
- **NOTE — bridge else/elif fidelity is NOT done** (see M12 item 5). Both
  `EXPR_IF` (bridge_part1:320) and `STMT_IF` (:466) convert only the then-body
  and pass `nil` for else, ignoring elif chains; `EXPR_IF` reads the STMTS
  slot while `expr_if_expr` stores then in RIGHT, so block-form if-EXPRESSIONS
  bridge to an empty then-block. Latent today — the seed compiles src/compiler,
  so the lean bridge's if-path isn't exercised in production. Tracked, not
  worked around: G42 is "parser accepts if-then-else", not "if-then-else DONE".

#### G45 — colon-ternary `if X then Y else: Z` — PARSER DONE 2026-06-13
The colon form (`else:` / `then:`) is MORE common than plain `else` in the
codebase (154 vs 54 sites; e.g. native.spl:368 `if use_lto then "-flto " else:
""`), so G42 alone was incomplete. In parse_if_expr's ternary branch, consume
an optional `:` (161) after `then` and after `else` before parsing each branch
expr. Round-2 (tmp/site12/g45_colon_seed.spl): else_colon / then_colon_else_
colon → false; plain `else` (G42) and block-form `if c:\n…\nelse:` BOTH
unregressed (block form never enters the ternary branch — it has `:` after the
cond, not `then`); control true.

#### G43 — open-ended slice `arr[N..]` — PARSER DONE 2026-06-13
`parse_range` (parser_expr.spl:276) always called `parse_addition()` for the
upper bound, so `arr[1..]` choked on `]` (`parts[1..].join(...)` in
query_engine/query_visibility). Fix: after consuming `..` (165), if the next
token cannot start an expression (`]`145 `)`141 `,`160 `}`143 Newline180
Dedent182 EOF190), emit `expr_range(left, expr_int_lit(-1), 0, 0)` — reusing
the parser's established "-1 = to end" sentinel (same one the colon-slice
`[start:]` path uses). `..=` still requires a bound (inclusive-open is
malformed). Round-2 (tmp/site12/g43_slice_seed.spl): open_slice_join /
open_slice_bare → false; bounded_slice (`a[1..3]`) and normal_range (`0..n`)
unregressed; control true. Target AST `Range(Expr?, Expr?, bool, Expr?)` has
optional bounds — a future refinement could carry None instead of -1.

#### G44 — postfix `!` force-unwrap `expr!` / `expr!.field` — PARSER DONE 2026-06-13
Pervasive (57 files: `loc!.` ×112, `func!.` ×43, `best!.` etc.;
dwarf_parser.spl:44 `best!.address`). `!` lexes to kind 57 (TOK_NOT); in
postfix position (after a primary) a `!` is always force-unwrap — prefix-not
is consumed before the primary. Added kind-57 case to BOTH postfix loops
(parse_postfix + parse_postfix_on, parser_expr.spl) → `expr_exists_check`.
Round-2 (tmp/site12/g44_bang_seed.spl): bang_field / bang_method / bang_bare /
bang_field_cmp → false; prefix_not (`if not done:`) unregressed; control true.
- **NOTE — semantic fidelity:** `!` is parsed as the unwrap-family
  `EXPR_EXISTS_CHECK` (the only unwrap node; target AST has no ForceUnwrap).
  So `expr!` and `expr.?`/`expr?` currently produce identical AST; the
  force(panic)-vs-exists(nil) distinction needs a dedicated ForceUnwrap
  ExprKind — tracked M12 item 7. G44 is "parser accepts `!`", not full fidelity.

#### Broad construct sweep — src/lib parse coverage CLEAN 2026-06-13
After G42–G45, a 12-construct synthetic sweep (tmp/site12/g46_sweep.spl,
seed-interpreted) parses CLEAN for: list comprehension (+ `if` filter), dict
literal, lambda `fn(x)->T:`, nested generics `Map<K,List<V>>`, single method
chain, multiline-paren expr, match expression, string escapes, `??`, `?.`.
Cross-checked against the post-G42 wm_quality_contract residue (58 ctx errors,
ALL src/app): every non-spec-DSL error was a G43 (`query_* [N..]`), G44
(`dwarf* !.`), or G45 (`native else:`) class — all now fixed. The leftover
src/app residue is spec-DSL (`describe`/`it`, vscode examples, lint_spec) +
`m{…}` math blocks, which are OUT OF SCOPE for the src/lib gate (test/spec
files go through the sspec pipeline, not the core lean parser).
- **G46 — set literal `s{1,2,3}` — SKIPPED (not a gate blocker):** the only
  sweep construct that fails. `SetLit` exists in the AST but the `s{…}` form is
  effectively unused in src/lib (3 grep hits, all false positives — docstrings/
  config). If a real src/lib use surfaces later, add `s{`/`m{` as allowlisted
  prefix-block literals (see memory: never "any ident + `{`").

#### Post-perf gap-class wave (2026-06-13) — sweep unblocked by the env-mirror perf fix
With compiled parse now linear (M12-4 prerequisite met), per-file `check` sampling
(parser resyncs at file boundaries → primary errors, not the cascade-inflated
text.spl-closure count) shows **most src/lib files already parse clean** (~23/24 in
the common/ + nogc_sync_mut/ sample). Two gap classes found and FIXED:
- **G47 — `else if` (C-style elif), PARSER DONE + pushed.** 1001 sites across 164
  src/lib files (the dominant residue). Both if-statement else-handlers now parse a
  following `if` as a nested if (elif chain) instead of expecting `:`.
- **G48 — colon-form inline ternary `if C: T else E`, PARSER DONE + pushed.** ~29
  src/lib sites (e.g. `val s2 = if s < 0: s + N else s`). parse_if_expr's block-path
  else branch now distinguishes block `else:` / `else if` / inline `else EXPR`.
- **G49 — struct-literal `Name { field: value }`, DONE end-to-end + pushed
  (2026-06-13, commit 0e63bd973ff).** Was the DOMINANT remaining src/lib parse
  blocker (import-amplified: 13/24 sampled files). `expr_struct_lit`/EXPR_STRUCT_LIT
  existed with zero parser callers. Added `parse_struct_lit_tail` in both
  `parse_postfix`/`parse_postfix_on` loops, fired on `ident/dotted-path` base + `{`
  (Simple blocks are colon+indent, never brace → unambiguous). Field entries built
  as `expr_field_access(value,name)` carriers matching the flat-bridge layout.
  Verified on stage4 lean frontend: `Point{x:3,y:4}`→`p=3,4`, nested
  `Box{origin:Point{...},w:5}`→`b=10,20,5` at runtime (parse→bridge→HIR→codegen).
  See `doc/08_tracking/bug/lean_parser_struct_literal_unimplemented_2026-06-13.md`.

Remaining known gap classes (long tail, deferred):
- **G50 — default parameter values `fn f(x: T = expr)` — PARSER + IR-capture DONE
  + pushed (2026-06-13, commit fce662c707d1); call-site application is a
  DEPLOY-BLOCKER (open).** Parser accepts `= expr` in both param sites
  (parse_fn_decl + parse_class_body_method); defaults captured via
  `decl_set_param_defaults` → flat bridge `Param.has_default/default` → `HirParam`
  (faithful capture, not discarded). Cleared mcdc.spl:187. Explicit-arg calls
  correct on stage4 (`greet("hi",5)=10`). **BUT omitted-arg calls silently pass 0**
  (`greet("hi")=0`, not 6) — the self-hosted path has no value-arg arity check or
  call-signature resolution to fill defaults; that is its own milestone and a
  deploy-blocker (see M12 gate + `doc/08_tracking/bug/lean_parser_default_param_call_fill_2026-06-13.md`).
- **`extern class Name:` declaration form** — `extern fn` is handled but not
  `extern class` (runtime-type binding with fields). Only ~2 src/lib sites
  (error.spl SimpleError). Low priority.
- A clean full per-file src/lib sweep (now feasible) is needed to enumerate the
  rest; the historical text.spl-closure 1238 count is ~10× cascade-inflated and not
  a class count.

#### M12 remaining
1. Interpreted `flat_ast_to_module` entry OOB (see above) — diagnose/fix.
2. Verify `SIMPLE_BOOTSTRAP_DECL_*` env-var transport covers all new AST node types from M1–M11.
3. Remove `simple_seed` delegation guards from `src/app/cli/check.spl` and lint entry.
3b. **default-param call-site application — DONE on the active (Rust) frontend
    (2026-06-14, commit 4e151c2649b).** Default param VALUES parse + capture into
    the IR (G50); the deployed `run`/`jit`/`aot` path (Rust HIR frontend) now fills
    omitted trailing CONSTANT defaults at the call site
    (`Lowerer.fn_param_defaults` + `collect_fn_param_defaults` → fill in `lower_call`).
    Verified: `greet("hi")`→103, `multi(1)`→31, no-default `add(2,3)`→5; regression
    spec `test/01_unit/compiler/default_param_call_fill_spec.spl`. REMAINING for the
    self-hosted frontend deploy: the `.spl` `35.semantics` fill
    (`MethodResolver.fill_call_defaults`) must reach parity (currently inert; blocked
    by LIM-010) before delegation is removed, else self-hosted omit-calls miscompile.
    Follow-ups: method/`Path`-callee and cross-module imported-callee defaults.
    Bug: `doc/08_tracking/bug/lean_parser_default_param_call_fill_2026-06-13.md`.
4. **Gate:** `docker run --rm simple-stage4 bin/simple check src/lib/common/text.spl` exits 0; full 1855-file sweep reports 0 errors.
   **PREREQUISITE (perf) — ROOT CAUSE FOUND & FIXED 2026-06-13:** the superlinear
   `check` was the **per-index env-var AST mirror**, not type inference (an interim
   re-profile guessed "type inference" — superseded). Every `stmt_alloc` wrote 6
   `SIMPLE_BOOTSTRAP_STMT_<idx>_<field>` env vars and `expr_alloc` ~10; the keys are
   per-index unique so `environ` grows O(nodes) and libc setenv/getenv linear-scan it
   → O(N²). Across an import closure (one accumulated AST via `parse_module_file`)
   `module_add_decl`'s per-decl key compounds it. **FIXED** (committed): the per-index
   env writes (`stmt_*_set`, `expr_*_set`, `module_add_decl`) are gated behind
   `SIMPLE_BOOTSTRAP=1`; compiled stage4 uses the parallel module-var arrays
   (`*_get_*` readers are env-first/array-fallback, all arrays populated — verified).
   Measured (host stage4, synthetic N-function `check` wall): 52→15.3s, 146→20.4s,
   >300(timeout)→39.4s; 200→400 ratio 2.8×→1.9× = **linear**. Correctness: compiled
   stage4 compiles+runs a construct-varied program with exact output; g45/g46 green;
   parse errors=0. **Prerequisite MET — per-file parse/check is now linear.** Latent
   SECONDARY (dead today): `generalize_all`/`env_free_var_ids` in
   `30.types/type_infer/generalization.spl` (linear-scan sets) — fix when
   `infer_module` is wired. See doc/08_tracking/bug/ast_env_var_quadratic_parse_2026-06-13.md
   and interp_parse_superlinear_2026-06-12.md.
6. **Bridge if/else fidelity** (surfaced by G42): **DONE 2026-06-13, commit
   2e08f8eddf3d.** `EXPR_IF`/`STMT_IF` in _FlatAstBridge/convert_nodes.spl hardcoded the
   If else slot to `nil`, dropping every else branch and elif chain when the
   self-hosted lean frontend builds a Module. Fix: STMT_IF reads the else body
   from the elif arena via `elif_get_else(stmt_get_type(idx))`; EXPR_IF reads
   then from RIGHT and else from EXTRA, wrapping block-exprs/ternary branches via
   the new `flat_if_branch_block` helper (`EXPR_BLOCK`=18 → STMTS, bare expr →
   single-stmt block; `EXPR_UNIT`=33 in EXTRA = no else). `nil` is preserved when
   there is no else so codegen sees None vs Some(empty); elif chains are nested
   If nodes that convert recursively.
   **Verification (structural, discriminating):** the bridge is reachable today
   only via `check` under the delegation guard (`SIMPLE_FRONTEND_DELEGATED=1`);
   `run`/`jit`/`aot`/`native-build` use a separate Rust-backed frontend, and the
   lean `check` is too lenient (no name-resolution / return-type checking) to
   exercise a dropped else. So verification introspects the bridge's Module
   output directly: `test/01_unit/compiler/frontend/flat_ast_if_else_bridge_spec.spl`
   asserts the produced `ExprKind.If` carries an else block (`else-stmts=1`) for
   if/else and if/elif/else, and `nil` (no spurious empty block) for plain if.
   Confirmed before/after on the seed: buggy bridge → all `no-else`; fixed →
   `1 / nil / 1`. **Runtime-codegen proof is deferred to M12** — once delegation
   is removed and the bridge becomes the universal frontend, the same spec gains
   an executable end-to-end variant.
7. **ForceUnwrap fidelity** (surfaced by G44): **DONE 2026-06-13, commit
   61a7b960baf9.** Postfix `!` parsed as `expr_exists_check`, conflating
   force-unwrap (panic-on-nil) with `.?` (nil-on-absent) — both collapsed to
   `ExprKind.ExistsCheck`. Fix adds the full distinct pipeline: `EXPR_FORCE_UNWRAP`
   (=53) tag + `expr_force_unwrap` constructor; the parser `!` sites (token 57)
   build force-unwrap; a new AST `ExprKind.ForceUnwrap(Expr)` variant; bridge
   `EXPR_FORCE_UNWRAP → ExprKind.ForceUnwrap`; and HIR lowering to the existing
   (until now unproduced) `HirExprKind.Unwrap`. Safe: HIR consumers
   resolve/effect_pass/safety_checker already match `Unwrap`; narrowing/expr_infer
   wildcard it; the only AST-level `ExprKind` match (hir_lowering/expressions.spl)
   got the `ForceUnwrap` case. **Verification (structural, discriminating):**
   `test/01_unit/compiler/frontend/flat_ast_force_unwrap_spec.spl` walks the bridge
   output and asserts `x!` → ForceUnwrap, `x.?` → ExistsCheck. Confirmed before/after
   on the seed: buggy → both `exists-check`; fixed → `force-unwrap` / `exists-check`.
   **Panic-on-nil codegen of `HirExprKind.Unwrap` is deferred to M12** (same
   verification ceiling as item 6 — bridge reachable today only via the
   delegation-guarded `check` path).

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

---

## 2026-07-07 — Current full-CLI-redeploy blocker gaps (Task #21)

Three surface-form gaps still block a working full-CLI self-host, all reproduced on
the deployed binary 2026-07-07. Detailed grammar/parser/HIR designs and acceptance
criteria live in the design pair
`doc/05_design/compiler/parsing/frontend_parser_gaps_and_lazy_closure_design.md` §2;
the tracked execution plan is
`doc/03_plan/compiler/self_hosted_frontend/full_cli_redeploy_and_browser_startup_plan.md`
(Track A). Root-cause evidence:
`doc/08_tracking/bug/bootstrap_stage4_graph_load_timeout_2026-07-05.md` §4.

| # | Gap | Verified failing file:line | Parser error | Parser area |
|---|-----|----------------------------|--------------|-------------|
| A1 | array-repeat **expression** `[v; n]` (the value form; the `[T; N]` **type** form is already handled at `core/parser.spl:523`) | `src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl:257,265`; `src/lib/common/ui/window_scene_draw_ir.spl:148,232` | `expected ], got ; ';'` | `core/_ParserPrimary/primary_expr.spl:503-513` — add `;`-repeat branch (non-literal counts require a repeat AST node, not parse-time expansion) |
| A2 | `mut` parameters (74 files) | `src/compiler/mir_opt/mir_opt/pattern_dispatch.spl:193` | `expected ), got Ident` | `parser_types.spl:139` `struct Param` has no `is_mut`; add field + consume leading `mut` in param parser |
| A3 | irrefutable destructuring `val PAT = EXPR` (226 files) | `src/std/nogc_sync_mut/env/variables.spl:358` | self-host: `expected =, got (`; interpreter parses but HIR let-lowering rejects (`complex patterns not yet supported in let bindings`) | `val`/`var` stmt parser + HIR let-lowering (reuse the `match` pattern parser/lowering — largest change, land last) |

Divergence note: A2/A3 are cases where the interpreter parser accepts more than the
self-hosted `parse_full_frontend`; the fix makes **both** accept the same grammar, not
the self-hosted parser reject less. Verify each with BOTH `simple run` and `simple check`.
