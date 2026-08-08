# Pure-Simple parser did not implement the pipe-lambda form `|x| ...` at all — latent Stage-3 self-host blocker

- **Date filed:** 2026-08-08
- **Status:** **FIXED 2026-08-08.** The pipe-lambda production is implemented in
  the pure-Simple parser and gated by
  `scripts/check/check-pure-simple-pipe-lambda-parse.shs`. One follow-up remains
  OPEN — see *Remaining gap* below: per-param types are parsed and validated but
  then dropped, because the flat AST has no slot for them.
- **Area:** compiler / pure-Simple frontend parser (`src/compiler/10.frontend/**`)
- **Severity:** blocker-class for self-host, latent behind earlier Stage-3 blockers
- **Rule context:** `rust is seed and pure simple must impl and verified and used`

## Summary

Commit `150a24e0fdb` ("fix(parser): support typed pipe-lambda params
`|x: i64| ...`") fixed the **Rust seed parser only**. The spec that shipped with
it, `test/01_unit/language/typed_pipe_lambda_param_spec.spl`, says so in its own
header.

Nobody checked the pure-Simple side. On inspection the pure-Simple parser was not
merely missing the `: Type` annotation the seed fix added — **it did not implement
the pipe-lambda form at all**, neither `|x: i64| x + 1` nor the untyped `|x| x + 1`.

This is the reverse of the usual seed/pure-Simple gap: the seed was ahead by a
whole grammar production, and the deliverable implementation could not parse a
form that the language spec defines and that the pure-Simple compiler's own source
already uses.

## Evidence (as filed)

**1. No PIPE-token entry point in the primary-expression dispatcher.**
`src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl` never tested token
kind `121` (`TOK_PIPE`). The only lambda forms it accepted were `\params: body`
(backslash), `fn(...)` (inline fn lambda), and `&:method` (method reference).

**2. Every `|` site in the pure-Simple parser was a non-lambda use.**
`lexer_struct.spl:1473-1481` (emits `|>`/175, `||`/56, else plain `|`/121);
`parser_expr.spl:421-424,508-511` (binary bitwise-or); `parser.spl:953,958` and
`parser_stmts.spl:1417,1477,1609` (match-arm pattern alternation);
`asm_match_suffix.spl:67`, `parser_asm.spl:33`, `enum_module_body.spl:376`
(asm target spec / enum variant separator).

**3. The seed had the production; pure-Simple did not.**
`src/compiler_rust/parser/src/expressions/postfix.rs:975` —
`parse_pipe_lambda_params`.

**4. The form was already load-bearing in pure-Simple source.** 29 call sites
under `src/compiler`, 3 under `src/lib`. Concrete sites in
`src/compiler/35.semantics/error_formatter.spl`:442, :465, :475
(`elements.map(|e| self.format_type(e))` and siblings).

**5. The language spec has the form the hand-written parser lacked.**
`src/compiler/90.tools/verify/verify_treesitter_grammar.spl:90` lists a
`pipe_lambda` grammar node.

**6. Even with the production added, the flat-AST bridge drops the types.**
`_FlatAstBridge/convert_nodes.spl:948-953` hard-codes `has_type_: false`;
`expr_lambda` carries only `[i64]` ident indices with no parallel type vector.
This one is still open — see *Remaining gap*.

## Why it never surfaced as a Stage-3 failure

Stage 3 currently fails earlier, on module-resolution blockers (`unresolved type:
ByteOrder` in `cache_validator.spl`, then the `Effect` facade collision in
`src/compiler/50.mir/__init__.spl` — see
`doc/08_tracking/bug/t3_full_bootstrap_stage3_unresolved_type_byteorder_cache_validator_2026-08-06.md`).
Those fire before compilation reaches `src/compiler/35.semantics/`, so the parser
gap was **latent**: not the current Stage-3 error, but on the path to it.

It was also invisible day to day because `bin/simple run` and `bin/simple test`
parse with the **Rust seed**, which accepts `|e|`. Only `bin/simple lint` runs the
pure-Simple frontend.

## Fix as landed (2026-08-08)

`src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl` — a pipe-lambda
production in `parse_primary_expr`, placed immediately before the backslash-lambda
branch, mirroring the seed's `parse_pipe_lambda_params`. Accepts `|x|`, `|x, y|`,
`|_|`, `|x: i64|`, and the zero-param `| |` — written with a space because `||`
lexes as `TOK_OR`/56 in `lexer_struct.spl`, seed-side too, so this is the seed's
grammar and not a divergent dialect.

Per-param types use `parser_parse_type` (single type), **not**
`parser_parse_type_with_union`, which continues through `|` and would swallow the
lambda's own closing pipe — the exact trap the seed fix hit.

### Disambiguation — every pre-existing `|` meaning, verified not argued

The production is reachable **only in prefix (primary-expression) position**, so
an infix or separator `|` never reaches it. Every row below is covered by a
fixture in the gate script, and every row was linted green **both** with the fix
in place and with it reverted:

| meaning | form | who consumes the `|` | fixture |
|---|---|---|---|
| bitwise-or (infix) | `a \| b`, `(a \| b) \| 1`, `e = e \| b` | precedence climb, `parser_expr.spl:421,508` | `r1_bitor` |
| logical-or | `a \|\| b` | separate token `TOK_OR`/56, `lexer_struct.spl:1473` | `r2_logor` |
| union type | `x: i64 \| text` | `parser_parse_type_with_union` | `r3_union_type` |
| match-arm alternation | `case A \| B:` | `parser_stmts.spl:1417,1477,1609` — advances past `\|` first | `r4_enum_alt` |
| backslash lambda | `\x, y: x + y`, `\: 7` | the branch immediately after this one | `r5_bslambda` |
| line-leading `\|` continuation | `val c = a` ⏎ `    \| b` | `lexer_struct` leading-operator continuation | `r6_leading_pipe_cont` |
| pipe operator | `n \|> twice` | separate token 175 from the lexer | `r7_pipe_op` |
| enum variant separator | `Escape \| F1 \| F2` | `enum_module_body.spl:376` — own loop, advances then `continue`s | `r8_enum_sep` |
| asm target spec / clobber | `case [x86_64 \| x86]:` | `parser_asm.spl:33`, `asm_match_suffix.spl:67` — own `TOK_PIPE` loops | in-tree `test/01_unit/compiler/native/asm_match_spec.spl` |

`r6` is the one worth calling out. `check-seed-parse-superset.shs` documents that
the leading-operator line continuation is guarded by
"operator-cannot-begin-a-statement" — a predicate that was trivially true of `|`
before this change and is not any more. If that guard ever consults a
"can this token start an expression" table, `r6` is what goes red.

### Controls and results

`bin/simple lint` runs the pure-Simple frontend **from source** — proven, not
assumed. Reverting `primary_expr.spl` to its pre-fix blob
`5d8cd86aa8372aa3374251a6a4f8cc068505d5a0` made exactly the four pipe-lambda
fixtures report `PARSE001: unexpected token in expression: | '|'`, while all nine
`|`-meaning fixtures stayed clean; restoring blob
`4b095554e9bc6fdc5130a81c2b5db91188bb4820` made all thirteen parse. The deployed
binary `bin/release/x86_64-unknown-linux-gnu/simple` was not rebuilt or redeployed
in either direction, so the stale-lint-binary trap that
`scripts/check/check-lint-binary-staleness.shs` exists for does not apply here.

The gate has been observed **both** green and red:

```
$ sh scripts/check/check-pure-simple-pipe-lambda-parse.shs        # fix present
PASS — 13 fixture(s) checked: 4 pipe-lambda forms parse, 9 pre-existing `|` meanings intact

$ sh scripts/check/check-pure-simple-pipe-lambda-parse.shs        # fix reverted
FAIL — pure-Simple parse failure in: p1_single p2_typed p3_multi p4_zero (of 13 fixtures)
```

Note the red run names **only** the `p*` fixtures: reverting the production breaks
the pipe lambdas and nothing else, which is the same statement as "the production
steals no pre-existing meaning", read from the other direction.

Because lint **fails open** on unparseable input — a `PARSE001` means every
AST-based lint was skipped for that file — all assertions are on the `PARSE001` /
`NOT LINTED` markers, never on lint's exit code. Conversely a `STUB001` finding on
the union-type fixture is positive evidence of parse success: AST-based lints only
run on files that parsed.

Real call sites: `src/compiler/35.semantics/error_formatter.spl` (the `:442,465,475`
sites) and `src/compiler/20.hir/hir_lowering/types.spl` both lint with 0 errors and
no `PARSE001`.

### Remaining gap (still OPEN)

Evidence item 6 is unchanged. The parser now **accepts and validates** `|x: i64|`
and then drops the annotation, exactly as `parse_fn_lambda_after_kw` already does
for `fn(x: i64)` lambdas. That is parity with the pre-existing behaviour of the
other lambda forms, not a new hole — but widening `expr_lambda` to carry per-param
types and un-hard-coding `has_type_: false` in
`_FlatAstBridge/convert_nodes.spl:948-953` remains to be done before typed
pipe-lambda params are semantically honoured.

## Related

- `150a24e0fdb` — the seed-only fix that prompted this audit.
- `doc/08_tracking/bug/pipe_lambda_typed_param_parser_gap_2026-08-07.md` — the
  seed-side bug doc; it scopes itself to the seed and does not mention the
  pure-Simple parser.
- `test/01_unit/language/typed_pipe_lambda_param_spec.spl` — the seed-lane spec.
- `scripts/check/check-pure-simple-pipe-lambda-parse.shs` — the permanent gate.
- `doc/08_tracking/bug/t3_full_bootstrap_stage3_unresolved_type_byteorder_cache_validator_2026-08-06.md`
  — the Stage-3 blockers that masked this one.
