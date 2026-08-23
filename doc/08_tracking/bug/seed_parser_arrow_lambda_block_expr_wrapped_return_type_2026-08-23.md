# Seed parser: three grammar gaps blocking 5 specs at parse time (2026-08-23)

## Status update 2026-08-23 (second pass) — D1/D3/D4/D5 FIXED, D2 still OPEN

Everything below this box is the original filing and is left intact for
history; it is accurate about the defects, and one of its per-parser guesses is
corrected here by measurement rather than by inference.

**Twin check, measured in both implementations** (per the standing "a defect
found in one parser requires checking the other" rule). The pure-Simple
frontend was probed through `parse_full_frontend` on source strings; the Rust
seed through `<seed> run` on the minimal repros. Both halves are now pinned by
`test/01_unit/compiler/frontend/parser_arrow_lambda_and_continuation_indent_spec.spl`.

| gap | Rust seed (pre-fix) | pure-Simple frontend (pre-fix) | fixed in |
|---|---|---|---|
| D1 `(x) => e`, `(x, y) => e` | broken | broken | **both** |
| D1 `() => e` (zero-param) | already worked | **broken** — the original filing did not test this half | frontend |
| D1 bare `x => e` | broken | broken | **neither** — see below |
| D2 braced block expr | broken | broken | neither — still OPEN |
| D3 wrapped return type | broken | **twin ABSENT (parses fine)** — filing said "unverified"; now measured | seed |
| D4 `new` over-reserved | broken | **twin ABSENT (parses fine)** | seed |
| D5 wrapped `if` condition | broken | **twin ABSENT (parses fine)** | seed |

**D4 root cause was not what the filing guessed.** It is not a dispatch-order
problem and `TokenKind::New` is not consumed early: `identifiers.rs` reaches
its `parse_keyword_identifier("new")` arm normally. The abort came from the
COMMON-MISTAKE detector, `error_recovery.rs:386` (`CommonMistake::JavaNew`),
which flagged any `new` whose PREVIOUS token was not on a hand-maintained
denylist. `for new in [...]` has `for` as its previous token, which the list
never listed. Fixed by giving the rule the positive lookahead the neighbouring
`function` rule already uses — the Java mistake is `new Type(...)`, so it is
only flagged when an identifier FOLLOWS. That strictly narrows the heuristic:
every real `new Type(...)` diagnosis is kept.

**D3 and D5 are the same defect class**, not two: a header (a function
signature, or an `if` condition) wrapped onto a continuation line that sits at
exactly the BODY's column consumes the only INDENT the lexer emits, and the
body then starts with no INDENT of its own while the parser still demands one.
D5 turned out to have **two** shapes in that one product file, failing through
different code paths and needing two edits: the BLOCK then-branch at
`riscv_scalar_csr_owner.spl:48-52` ("expected Indent, found FString") and the
INLINE then/else at `:139-141` ("expected expression, found Dedent" — the
inline path never reconciled the continuation's pseudo-INDENT at all, whereas
the block path at least drained the "Deep" case). Fixing only the first moved
the error from line 50 to line 141 and left the spec at `executed=0`, which is
why both are fixed here. With both fixed, `formal_verification_2_0_spec.spl`
goes **executed 0 -> 81, passed 73, failed 8** — the 8 are ordinary assertion
failures in a spec that had never executed at all, not parse errors, and are
outside this record's scope. The
`for`/`while` statement forms already carried a guard for this exact shape
(`header_continuation_is_equal_column`, from
`seed_elif_while_condition_continuation_indent_ambiguity_2026-07-31.md`); the
fixes bring the function-signature and if-EXPRESSION forms in line with it
rather than inventing a new rule. One extension was needed: the shared
`is_statement_start()` predicate lists only statement keywords and identifiers,
so an expression block starting with a literal (`"completion_" + field[0]`) was
not recognised as a body start; that widening is local to the if-expression
path so the loop guards are untouched.

**D1 landed in BOTH parsers, as the filing required** — the parenthesised form
only. Bare `x => e` is implemented in NEITHER, deliberately: it needs an
identifier-position lookahead sitting next to live match-arm `=>` handling
(seed `is_spurious_match_arm_fat_arrow`; frontend `parser_stmts.spl:1828`), and
`=>` is a real match-arm separator in product code (e.g.
`src/lib/nogc_sync_mut/engine/render/any_backend3d.spl:34-64`). The blocked
specs need only `(x) => x + 1`.

**D2 is a documented refusal, not an oversight.** A braced block in expression
position collides with four live productions that all begin with `{`: dict
literal `{k: v}`, empty dict `{}`, and dict comprehension
(frontend `_ParserPrimary/primary_expr.spl:797-885`; seed `parse_dict_literal`,
`primary/collections.rs:312`), plus the seed's brace-postfix method-call form
guarded by `no_brace_postfix`. Distinguishing them needs a real disambiguation
rule and a new AST node (or a `DoBlock` reuse) in both parsers, not a lookahead
tuned until the two blocked specs pass. The shape a future fix should
generalise is the seed's existing `peek_brace_is_lambda_block()`
(`primary/lambdas.rs:138`), today used only for `\`/`|` lambda bodies. D2 stays
OPEN and still blocks `nested_fn_capture_class_spec.spl` and
`parser_framework_spec.spl`.

---

Status: OPEN. Found while fixing the four "seed parser gaps" named by the
4,394-spec sweep (`PHASE1_SEED_CORE_SWEEP_2026-08-23.md`). Three of the eleven
blocked specs turned out to be **one** defect each in the Rust seed parser
(`src/compiler_rust/parser/`), all reduced to minimal repros below. They are
recorded rather than fixed in the same change because each is a real grammar
addition to the seed, not a one-line list entry like the soft-keyword gap that
*was* fixed alongside this record.

The impact is out of proportion to the spec count: a parse error makes the whole
file report `executed=0`, so every example in it is invisible in pass rates
rather than counted as failing.

## D1 — `=>` arrow lambda is not parsed at all

Minimal repro (both forms fail):

```simple
fn main():
    val f = x => x + 1        # error: expected expression, found FatArrow
    val g = (x) => x + 1      # error: expected expression, found FatArrow
```

In argument position the message differs but the cause is the same:

```simple
fn g(h: (i64) -> i64) -> i64: h(1)
fn main():
    print(g((x) => x + 1))    # error: function arguments: expected Comma, found FatArrow
```

The seed supports the backslash form `\x: expr` and, notably, the ZERO-parameter
arrow form `() => expr` — so the arrow lambda is not foreign to it, only its
non-empty parameter list is missing (see the parser table below). The arrow form
is used in the documented syntax reference
(`doc/07_guide/quick_reference/syntax_quick_reference.md:389`,
`nums.flat_map(x => [x, x * 10])`), so this is a seed gap, not an invalid
construct.

Blocked specs (2, a mirror pair):
- `test/01_unit/compiler/interpreter/callable_field_dispatch_spec.spl`
- `test/unit/compiler/interpreter/callable_field_dispatch_spec.spl`

Both use `LambdaFieldRoute(handler: (x) => x + 1)`.

## D2 — braced statement block `{ ... }` in expression position is parsed as a dict literal

Minimal repro, lambda body:

```simple
fn main():
    val lam = () => {
        val y: i64 = 5
        y + 1
    }
```
`error: Unexpected token: expected Colon, found Identifier { name: "y" }` — the
`{` was taken as a map literal, so `val` was read as a key and a `:` demanded.

Minimal repro, match-arm body (independent of D1):

```simple
fn pick(n: i64) -> i64:
    match n:
        0 -> 1
        _ -> {
            val z = 2
            z + 1
        }
```
`error: Unexpected token: expected Colon, found Identifier { name: "z" }`

Blocked specs (2):
- `test/03_system/interpreter/nested_fn_capture_class_spec.spl` (lambda body)
- `test/03_system/app/compiler/feature/parser_framework_spec.spl` (match-arm
  body — `Err(reason) -> { assert_true(...) \n parse_runtime_with_mode(...) }`)

Note this is the *only* thing wrong with `parser_framework_spec.spl`: its
multi-line braced `use ... { A, B as C }` import list, which the error message
superficially points at, parses fine (verified with a standalone fixture).

Disambiguating `{` here needs a real decision (lookahead for `key:` vs a
statement start, or requiring a distinguishing token), so it is filed rather
than patched with a fragile one-token guess.

## D3 — a return type wrapped onto continuation lines loses the body INDENT

```simple
fn pair(a: i64) ->
    (i64,
     i64):
    val z = a          # error: Unexpected token: expected Indent, found Val
    (z, z)
```
The same signature on one line (`fn pair(a: i64) -> (i64, i64):`) parses and
runs. So bracket continuation works; what fails is a line break immediately
after the trailing `->`, which leaves the body at an indentation the signature
parser has already consumed.

Blocked spec (1):
- `test/01_unit/os/kernel/loader/guest_toolchain_execution_authority_spec.spl`
  (`fn _chain_tokens(...) ->` at line 153, three-tuple return type on lines
  154-155).

**Deliberately not "fixed" by reformatting the spec.** Per the standing rule, a
short safe grammar form that fails is fixed or filed, never silently normalised
into a workaround.

## Scope verdicts

| gap | valid Simple? | parser at fault |
|---|---|---|
| D1 arrow lambda | yes — documented at `syntax_quick_reference.md:389` | Rust seed |
| D2 braced block expr | yes — used in committed specs, both lambda and match-arm bodies | Rust seed |
| D3 wrapped return type | yes — ordinary continuation formatting; single-line form works | Rust seed |

## Repro fixtures

The three repros above are self-contained and run directly with
`<seed> run <file>`; they need no stdlib beyond `print`.

## Which parser(s) are wrong — verified by source, not inference

Both parsers were checked: the Rust seed (`src/compiler_rust/parser/`) and the
self-hosted pure-Simple frontend (`src/compiler/10.frontend/`).

| gap | Rust seed | pure-Simple frontend |
|---|---|---|
| D1 arrow lambda | partial — `() => expr` IS supported (`expressions/primary/collections.rs:32-40`, builds `Expr::Lambda`), `(x) => e` and `x => e` are not | **no support at all** — `=>` (`TOK_FAT_ARROW`, `core/tokens.spl:134`) is handled only as a match-arm separator (`core/parser_stmts.spl:1828`); `parser/recovery.spl:93` errors on it explicitly |
| D2 braced block expr | no — `{` in expression position goes to `parse_dict_literal` (`expressions/primary/collections.rs:11`, defn `:312`); no `Expr::Block` variant exists (closest holder is `DoBlock`, `ast/nodes/core.rs:768`) | no — `{` is always dict / dict-comprehension (`core/_ParserPrimary/primary_expr.spl:797-885`) |
| D3 wrapped return type | yes, seed bug | unverified (frontend return-type path is `core/parser_decls_fn.spl`; continuation handling not confirmed) |

Consequences for how each should be fixed:

- **D1** is the cheapest and most self-consistent: the seed already has the
  zero-parameter arrow lambda, so `(x) => e` is the *same production* with a
  non-empty parameter list. Insertion point is `parse_grouped_or_tuple`
  (`expressions/primary/collections.rs:20`, after `let first =
  self.parse_expression()?` at `:45`), reusing `Expr::Lambda` /
  `LambdaParam { name, ty }` (`expressions/primary/lambdas.rs:45,123`). A bare
  `x => e` would additionally need a lookahead in `parse_primary`
  (`expressions/primary/mod.rs:158`) before identifier dispatch. **But fixing
  the seed alone creates parser divergence**, because the frontend has no arrow
  lambda whatsoever — so D1 must land in both parsers or in neither. That is
  why it is filed and not patched here.
- **D2** needs a new AST node (or a `DoBlock` reuse) *and* a `{` disambiguation
  rule in both parsers. The seed already has one narrow precedent —
  `peek_brace_is_lambda_block()` (`expressions/primary/lambdas.rs:138`), used
  only for `\`/`|` lambda bodies — which is the shape a general rule should
  follow rather than a fresh ad-hoc lookahead.
- **D3** is genuinely seed-local and the smallest: the lexer already suppresses
  INDENT inside brackets (`lexer/mod.rs:24,131,188,197-217`,
  `lexer/indentation.rs:239`, with a `force_indent_bracket_depths` override
  stack at `lexer/mod.rs:31,74,81,92`), so `(`…`)` across lines is fine. The
  defect is the *parser's* `sig_indents` bookkeeping around the trailing-`->`
  continuation drain: `parser_impl/functions.rs:103` and `:109-130` (drain),
  versus the body-INDENT expectation at `:195-201`; a second copy of the same
  shape is at `:540` / `:554`.

## Related, already tracked separately

`test/01_unit/compiler/resource/resource_sffi_pilot_spec.spl` also reports
`executed=0` in the same sweep (`expected Fn, found Identifier "resource"`).
That one is **not** a grammar defect and is deliberately RED: the spec's own
header states `resource` is an intended surface that is not a parsed
declaration kind in either parser, tracked by
`doc/08_tracking/bug/resource_decl_and_sffi_attribute_not_parsed_2026-08-07.md`.
It is a feature gap, not a parser bug, and is not addressed here.

## D4 — `new` is still over-reserved (newly EXPOSED, not caused, by the `case` fix)

Un-reserving `case` let `soft_keyword_identifier_corpus_spec.spl` parse for the
first time (0 -> 9 examples executed). 7 of the 9 pass; the failures isolate to
one word:

```simple
fn main():
    var t = 0
    for new in [1, 2]:
        t = t + new      # error: Common mistake detected: Use struct literal: Type { field: value }
    print(t)
```

Every other word the corpus sweeps (`context feature scenario given when then
outline result out type default common lazy skip exists old from by mod union
examples case`) passes the same three-position fixture — verified one fixture
per word. `new` is the lone remaining outlier: it is still consumed as the
`new Type(...)` constructor keyword in expression position, even though
`identifiers.rs` already lists `TokenKind::New => parse_keyword_identifier("new")`,
so something dispatches `New` before that arm is reached.

This is the exact asymmetry the corpus spec was written to catch, and the spec
is doing its job: it now reports `executed=9 passed=7 failed=2` instead of
hiding everything behind a whole-file parse abort. Not fixed here — it is a
different token from the two this change un-reserved, and needs its own
dispatch-order investigation.

## D5 — a second parse blocker behind `formal_verification_2_0_spec.spl`

With `invariant` un-reserved that spec parses, but it then fails to compile on
*product source* it imports:

```
parse: in "src/compiler/50.mir/hwir/riscv_scalar_csr_owner.spl":
Unexpected token: expected Indent, found FString([Literal("completion_")])
```

So the spec goes `executed=0 reason=parse-error` -> `executed=0 outcome=ERROR`
with the error moved out of the spec and into a compiler module. Separate
defect, separate file, not addressed here.
