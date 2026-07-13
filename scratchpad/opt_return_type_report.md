# Optional return-type grammar fix — report

## Documented grammar findings

- `doc/05_design/language/language_features/control_flow/question_mark_design_decision.md:35`:
  "**Optional Type Syntax (implemented):** `T?` - Sugar for `Option<T>`" — this is the
  settled, implemented spelling: **suffix** `T?` (e.g. `i64?`, `[T]?`, `Option<T>`).
- `doc/07_guide/quick_reference/syntax_quick_reference.md` documents `T?` pervasively
  (the `.?` existence-check operator returns `T?`) but never documents a **prefix**
  `?T` return-type spelling.
- A handful of *design-phase* docs (`doc/05_design/lib/text_i18n/text_encoding_engine.md`)
  use prefix `?i64` as an aspirational example, but this was never implemented — it is
  not the current legal grammar.
- Confirmed empirically: the interpreter/seed oracle (`bin/simple run`, Rust-built
  binary reached via `env -u SIMPLE_BOOTSTRAP bin/simple run`) **also rejects** prefix
  `?i64` with `HIR lowering error: Unknown type: ?` / `cannot convert value to i64` —
  it is not a case where native diverges from an established grammar; prefix `?T` was
  never valid anywhere. Suffix `i64?` already worked correctly on **both** the oracle
  and the native `--entry` path before this fix.

Conclusion: `?i64` is not documented/legal syntax at all (only `T?` suffix and
`Option<T>` are). Per the task's HARD RULE, the correct minimal fix is a **clean loud
parse error naming the workaround**, not full grammar support for an unsupported
spelling — full support for the (already legal) suffix form required no fix at all.

## Root cause (file:line)

`src/compiler/10.frontend/core/parser.spl`, `fn parser_parse_type()` (was line 379-393,
the head of the function). When the current token is `?` (`TOK_QUESTION` = 130), none of
the type-form branches (`dyn`, ident/generic/suffix-`?`, array `[T]`, `fn(...)`, tuple
`(...)`, dict `{K:V}`) match, so control fell through to the catch-all at the old
line 625: `parser_error("expected type annotation"); TYPE_VOID` — which logs an error
but **does not consume the `?` token**.

Back in `parse_fn_decl()` (`src/compiler/10.frontend/core/parser_decls_fn.spl:153-155`),
`ret_type = parser_parse_type_with_union()` returns with the token cursor still sitting
on the unconsumed `?`. The next step, `parser_expect(TOK_COLON)` (line 169), then also
fails ("expected :, got ? '?'") because the current token is still `?`, not `:`. This
leaves the parser's error-recovery machinery to reinterpret the leftover `? i64:` as a
fresh expression/statement, which parses `i64` as a bare identifier expression — later
surfacing as HIR lowering errors `unresolved name: i64` and `unresolved name: n`
(the `n` parameter got orphaned by the desynced token stream, not because param
registration itself was skipped — param parsing at `parser_decls_fn.spl:121-147`
completes correctly *before* return-type parsing runs).

## Fix

Added a guard at the top of `parser_parse_type()`: when the leading token is `?`,
emit one located `parser_error` naming the workaround ("use suffix form `T?` ... or
`Option<T>` instead"), consume the `?`, and recursively parse the underlying type so
the token stream resyncs immediately (the following `:` for the function body is then
seen correctly by the caller). This converts the destructive cascade into a single
clean diagnostic with no follow-on param/body corruption. Net effect: 16 net new
lines in `src/compiler/10.frontend/core/parser.spl` (see
`scratchpad/opt_return_type.patch`).

Side effect (bonus, not required by the task): because the recursive call still
returns the *underlying* type (e.g. `TYPE_I64` for `?i64`), and this compiler's
codegen appears tolerant of `Some(...)`/`None` returns against a plain `i64` slot,
programs using prefix `?i64` now also produce the numerically correct output — but
they still emit the loud parser error, so this is not a silent-wrong regression risk;
it's strictly better than before (error + correct value, vs. error + destroyed params).

## Battery table (native `--entry` path, `env -u SIMPLE_BOOTSTRAP bin/simple native-build --entry ... -o ... --clean`)

| # | Program | Return-type spelling | Expected (by construction) | Native output | Pass |
|---|---|---|---|---|---|
| 1 | `pick(n) -> i64?`, Some/None accumulate in `while` loop over main, values `n*3+1` non-multiple-of-8 | suffix `i64?` | `050` (0 then sum 4+7+10+13+16=50) | `050` | PASS |
| 2 | same as 1 but `-> Option<i64>` | `Option<i64>` | `050` | `050` | PASS (identical to suffix form) |
| 3 | `combine(a,b) -> i64?`, 2-param, Some(7)/None(2000) | suffix `i64?` | `02007` | `02007` | PASS |
| 4 | `triple(n) -> i64` (non-optional control) | plain `i64` | `050` | `050` | PASS (unaffected) |
| 5 | multi-construct: optional-return fn + `val (x,y) = (i, i*2)` tuple destructure + `while` loop | suffix `i64?` | `064` | `064` | PASS |
| C1 | `combine(a,b) -> ?i64` (prefix, the bug repro), 2-param | prefix `?i64` (illegal) | before fix: cascading `unresolved name: i64` / `unresolved name: n`, params destroyed. after fix: **one** clean `[parser_error] ... prefix optional type '?T' is not supported ...`, 0 "unresolved name" errors, params intact, binary still built and ran producing `07` (10-3=7 by construction) | matches | PASS (no cascade) |

All "Some" outputs above were verified **by construction** (arithmetic accumulation of
non-multiple-of-8 values), not via the interpreter oracle, since the oracle is known
to print garbage for `Some(v)` payload extraction (confirmed: oracle printed
`<value:0xf>` for the suffix-form single-fn repro while native correctly printed `15`).
None-arm oracle outputs and non-Option oracle outputs were used only for confirming
grammar legality (the prefix-form hard rejection), which is oracle-reliable.

## Smoke matrix summary

`sh scripts/check/native-smoke-matrix.shs` from the worktree:

```
total=15 pass=14 fail=1 xfail=0 xpass=0 codegen_fallback_hits=0
```

Only failure: `option_nil_check` (`(14) Option/nil check (x.?)`, got rc=1 want=7) —
this is the pre-existing allowed failure named in the task's gate criteria
(`>=14/15, 0 codegen_fallback_hits, only allowed fail = option_nil_check`). Gate: **PASS**.

## Outcome

**Full support achieved for the documented grammar** (`T?` suffix and `Option<T>`
already worked and continue to work, verified unaffected). For the **undocumented**
prefix `?T` spelling that was actually driving the bug report, achieved the task's
stated minimum acceptable outcome — a **clean, loud, located parse error naming the
workaround** — with no destructive cascade into param/body parsing, and as a bonus
the resync also happens to let the rest of the program compile and run with
numerically correct behavior.

## Files touched

- `src/compiler/10.frontend/core/parser.spl` — `fn parser_parse_type()`, added
  16-line guard for leading `TOK_QUESTION` (prefix `?`).
- No changes to `parser_stmts.spl` (avoided per instructions).
- No changes to `parser_decls_fn.spl` — param parsing there was already correct;
  root cause was entirely in the type parser's token-consumption discipline.

Patch: `/home/ormastes/dev/pub/simple/scratchpad/opt_return_type.patch`
