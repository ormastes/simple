# Bug: Self-Hosted Parser Cannot Parse Lambda Expressions in Call Arguments

**Date:** 2026-06-11  
**ID:** selfhosted_parser_lambda_gap_2026-06-11  
**Status:** Closed 2026-06-11
**Severity:** Was HIGH — blocked E-PAR-006 share-nothing lint from firing in the self-hosted lane

## Historical Symptom

All closure/lambda forms that produce `EXPR_LAMBDA` nodes fail to parse when used as
call arguments in the self-hosted parser. Tested forms and results:

| Form | Parser result |
|------|--------------|
| `green_spawn(\x: x + 1)` | `parser_error: kind 191 '\'` — backslash not recognised in expression position |
| `green_spawn(\: counter)` | same backslash error |
| `green_spawn(fn(): val x = 1)` | `parser_error: kind 20 'fn'` — fn keyword not recognised as expression in call arg |
| `green_spawn({ counter })` | parse error on `{` |
| `green_spawn(do: counter)` | **parses** but yields `EXPR_DO_BLOCK` (tag 44), NOT `EXPR_LAMBDA` (tag 26) |

## Affected Fixtures

- `test/fixtures/concurrency_api_misuse/green_spawn_shared_var_capture.spl`  
  Uses `\x: expr` form → parse errors → lint never runs on it.

## Impact on E-PAR-006 Self-Hosted Lane

`check_concurrency_share_nothing` (src/compiler/35.semantics/lint/concurrency_share_nothing.spl)
gates its lambda check on `expr_get_tag(first_arg) == EXPR_LAMBDA`. Since no parseable
closure form in call-argument position produces `EXPR_LAMBDA`, the lint's E-PAR-006
violation path **cannot fire** through the self-hosted parser. The lint logic is correct;
the parser is missing the lambda-in-expression production.

## Suspected Area

`src/compiler/10.frontend/core/` parser expression rules — the primary expression
parser (`parse_primary` / expression descent) does not handle:
- `\` as start of a lambda expression
- `fn` keyword as an anonymous function expression (only as top-level declaration)

## Resolution Required

Add lambda expression parsing so `\params: body` and `fn(params): body` are valid
primary expressions (usable as call arguments). Until fixed, all E-PAR-006 end-to-end
green tests that use lambda syntax are blocked in interpreter/self-hosted mode.

## Fix status (2026-06-11, later same day)

Expression-form backslash lambdas now parse self-hosted: `\: expr`, `\x: expr`,
`\x, y: expr`. Changes: TOK_BACKSLASH=220 (tokens.spl), `\` tokenized in all
three lexers (lexer.spl, lexer_struct.spl — the active one for parse_module —
and lexer_scanners.spl), lambda production in parse_primary_expr building
EXPR_LAMBDA per the eval_lambda contract (args = EXPR_IDENT params,
stmts = body EXPRS; block bodies wrapped in one EXPR_BLOCK). The E-PAR-006
lint's lambda handling was aligned to the same contract (it had walked body
exprs as stmt indices → OOB).

Verified end-to-end: green_spawn + multicore_green shared-var fixtures parse
(errors=false) and E-PAR-006 fires with the correct message via
check_concurrency_share_nothing.

Still open:
- Block-body lambda inside call parens (`spawn(\:` NEWLINE INDENT stmts `)`)
  still fails — newline/indent tokens inside parenthesized args; cooperative
  fixture remains seed-only.
- Pre-existing (NOT a regression; reproduced at HEAD before this change):
  parse_module on src/lib/nogc_async_mut/concurrent/green_thread.spl hangs
  >100s in interpreter mode.
- parse_module no-ops (errors=false, decls=0) on concatenation-built strings;
  only rt_file_read_text sources parse — interpreter string/env issue.
## Block-form fix (2026-06-11, follow-up)

Block-body lambdas inside call parens now parse. Token-stream evidence showed
the lexer emits INDENT (181) for the lambda body inside parens but no matching
DEDENT before ')' (dedents flush at EOF/outdent), so parse_block — which
requires a DEDENT terminator — errored at ')'. The lambda production in
parse_primary_expr now uses its own block loop: parse_block's shape plus ')'
(141) and ',' (160) as unconsumed terminators. Verified: the cooperative
fixture parses and E-PAR-006 fires with kind "captured mutable variable write";
expression-form fixtures and both lint specs (9/9, 44/44) unaffected. All three
shared-var fixtures now work end-to-end self-hosted.

## Multibyte stall + string-source no-op fixes (2026-06-11, follow-up 2)

- FIXED multibyte token-stream stall: CoreLexer pos walks slice units while
  len() counts bytes, so after any multi-byte UTF-8 char (→, — in comments or
  docstrings) pos exhausts the text before len(); handle_indentation then
  returned token-less and the stream stalled re-serving the last NEWLINE
  forever. at_end() now also treats an empty peek as end-of-input
  (lexer_struct.spl). Minimal repro (comment containing →) parses.
- FIXED parse_module string-source no-op: lex_init_with_path discarded the
  caller-supplied source whenever a path was given and re-read from disk; a
  virtual path made the source empty and the parse silently no-opped
  (errors=false, decls=0). Now the reread only replaces the source when
  non-empty (lexer.spl). Identical built-string vs file-read sources now parse
  identically.
## green_thread.spl parse hang fix (2026-06-11, follow-up 3)

**Root cause identified and fixed** in `src/compiler/10.frontend/core/lexer.spl`.

`lex_snapshot_save` / `lex_snapshot_restore` (used by `try_skip_ident_generic_args`
for speculative `<TypeArgs>` lookahead) did not save/restore the `CoreLexer.indent_stack`.
After each failed generic-arg probe the indent stack was silently reset to `[0]`
(hardcoded in `current_core_lexer_save`). In deeply nested code like join()'s
`while i < GREEN_TASKS.len():` (inside class → method → if → while), the next line's
indentation was measured against the wrong stack, producing spurious INDENT/DEDENT tokens
and causing `parse_block`'s 100,000-iteration loop to spin without progress.

**Fix:** `lex_snapshot_save` now serialises `lx.indent_stack` into `txts[1]` via
`current_core_indent_stack_format`. `lex_snapshot_restore` deserialises it back into
`lx.indent_stack` before writing to `current_core_lexer_slot[0]`.

**Verification:**
- Minimal reproducer (nested class→method→if→while with `i < ARRAY.len()` condition)
  parses: `errors=false decls=2` in ~7 s
- First 97 lines of green_thread.spl parse: `errors=false decls=10` in ~70 s
  (interpreter overhead, not a loop)
- All 5 regression baselines: `errors=false`, correct decl counts
- Lint specs: concurrency_share_nothing 9/9, concurrency_api_misuse 44/44

**Remaining pre-existing issues (not regressions):**
- Multi-line named-arg struct literals (`GreenTask(\n    field: val,\n    ...)`) emit
  parse errors for `,` and `:` tokens; this is a pre-existing parser gap unrelated to
  the hang fix. Full green_thread.spl parse completes (no hang) with these errors.

## Post-fix status (parse now terminates; perf bug remains)

With the snapshot indent-stack fix, truncated repros terminate and the full
file is no longer an infinite loop — but interpreted parsing is severely
superlinear: head-97 ≈ 70s, head-120 ≈ 148s, full 184 lines exceeds 420s
(confirming run with 1200s pending). Perf bug (record, not normalize): the
per-token env round-trips (SIMPLE_BOOTSTRAP_LEX_* save/restore on every
lex_next) plus speculative generic-lookahead snapshots dominate; related to
the known Rust-layer interpreter bottlenecks (debug_state mutex, Value::Str
copies, extern dispatch). Also pre-existing and separate: multi-line
named-arg struct literals inside parens emit parse errors for ','/':' tokens
(t120 shows errors=true decls=15 yet terminates).
