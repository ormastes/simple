# `case` is reserved everywhere, so `for case in …` kills the whole file at parse

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 00).
2026-08-10 re-triage below). The pure-Simple `.spl` frontend already accepts
`case` as a for-loop binding; only the seed lexer hard-reserves it. The one
spec it was blocking has been unblocked.
**Found:** 2026-08-04
**Severity:** medium — a parse error rejects the entire file, so one loop
variable cost every example in it, and `case` is not on the documented
reserved-word list

## Symptom

```sh
$ SIMPLE_TIMEOUT_SECONDS=0 bin/simple test --no-cache --no-cover-check \
    test/01_unit/lib/common/encoding/sfnt_spec.spl
error: compile failed: parse: in ".../sfnt_spec.spl":
       Unexpected token: expected pattern, found Case
Results: 1 total, 0 passed, 1 failed
```

The offending line was an ordinary `for` loop over a list of test scenarios:

```
for case in cases:
    val result = validate_default_glyf_font(case.1)
```

Expected: `case` binds like any other name outside a `match`. Actual: the
parser reaches `for`, expects a pattern, sees the `Case` token, and aborts —
taking all four examples in the 229-line file with it.

## Root cause

`case` is lexed as a keyword unconditionally, not as a soft keyword valid only
in `match` arm position. Nothing about `for <binding> in` is ambiguous with a
match arm: `case` in a binding position cannot be anything but an identifier,
because a match arm can only appear inside a `match` block.

The reserved-word list in `.claude/rules/language.md` reads:

> **Reserved keywords:** `gen`, `val`, `def`, `exists`, `actor`, `assert`,
> `join`, `pass_todo`, `pass_do_nothing`, `pass_dn`

`case` is not on it. So either the list is stale, or `case` is over-reserved —
and the diagnostic ("expected pattern, found Case") describes the parser's
internal state rather than telling the author that `case` cannot be a variable
name, which is what they need to know.

This is the same shape as `literal`, already filed as a silent soft-keyword.
The difference is the blast radius: `literal` misparses an expression, while
this one fails the compilation unit.

## What was changed

The loop variable in `sfnt_spec.spl:147` was renamed `case` → `scenario`, with
a comment pointing here. That took the file from `0 passed, 1 failed` to
`3 passed, 1 failed` — the parse error had been masking four real examples.

Per the repo rule ("when a short, safe grammar form fails … fix it or record a
concrete bug/feature request instead of silently normalizing the workaround"),
the rename is recorded here rather than left as an unexplained edit. The
grammar itself is untouched.

## Newly exposed, not yet diagnosed

With the file parsing, one of its four examples fails on real behaviour:

```
✗ matches preferred bounded Windows English names and rejects malformed records
  expected subject to be truthy, got false
```

That example (`sfnt_spec.spl:180-221`) makes roughly fifteen unlabelled
assertions against `sfnt_manifest_names_match` in a single `it`, covering
preferred-family (name IDs 16/17) precedence, lone-surrogate rejection,
truncated and odd-length name records, early storage offsets, and duplicate
ID conflicts. The runner reports only "expected subject to be truthy, got
false" with no indication of which assertion, because none of them carry a
message. Splitting that example into one `it` per property is a prerequisite
for diagnosing it, and is worth doing regardless.

## Why the grammar is not fixed here

Changing which tokens the lexer reserves affects every file in the tree and
belongs with the parser work already in flight (`parser_framework`), not in a
test-repair lane. The narrow fix — treat `case` as a soft keyword recognised
only in match-arm position — is the same change `literal` needs, so the two
should land together.

## Re-triage 2026-08-08 — STILL REPRODUCES; and it is BOTH front ends, not one

Binary: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple` (Rust
bootstrap-seed banner).

Standalone repro, no spec file involved:

```simple
fn main():
    var t = 0
    for case in [1, 2, 3]:
        t = t + case
    print "sum={t}"
main()
```

    error: compile failed: parse: Unexpected token: expected pattern, found Case

Identical to the 2026-08-04 transcript, so nothing has changed. Note the JIT
does not even get to try — it reports `JIT compilation failed, falling back to
interpreter: module load error: parse: ... expected pattern, found Case`, and
the interpreter then fails on the same parse. A parse error is engine-agnostic,
which is why this one reproduces everywhere.

**New fact worth recording, because it changes the scope estimate.** The report
above attributes the reservation to the seed lexer. It is a hard keyword in the
**pure-Simple** front end as well — `KwCase` is a distinct token kind in
`src/compiler/10.frontend` (token-kind table entry `KwCase  # case`, and it
appears in the keyword group alongside `KwIf | KwElse | KwElif | KwMatch |
KwFor | KwWhile`). So the soft-keyword change has to land in both front ends to
actually free the identifier; fixing only one leaves the other rejecting the
same file. That is a further argument for landing it with the `parser_framework`
work rather than as a drive-by.

**Secondary finding confirmed:** the reserved-word list in
`.claude/rules/language.md` still reads `gen`, `val`, `def`, `exists`, `actor`,
`assert`, `join`, `pass_todo`, `pass_do_nothing`, `pass_dn` — `case` is not on
it, and neither is `match`, `literal`, or the other hard keywords the lexer
actually reserves. The list is not a list of reserved words; it is a list of
*surprising* reserved words that has fallen out of date. Until the soft-keyword
change lands, `case` belongs on it, since being absent from that list is what
made this cost a whole file.

**Not fixed here** (unchanged from the original disposition): the grammar is
untouched, and the rename in `sfnt_spec.spl:147` remains the only mitigation.

## Re-triage 2026-08-10 — the 08-08 dual-front-end claim was WRONG; only the Rust seed reserves `case`

The 2026-08-08 note above claimed the pure-Simple `.spl` front end *also*
hard-reserves `case`, citing the `KwCase` entry in
`src/compiler/10.frontend/lexer_types.spl:50` and its membership in the
keyword group at `lexer_types.spl:216`. That citation is real but the
conclusion doesn't follow: `lexer_types.spl`'s `TokenKind`/`is_keyword()` is
used by the **treesitter outline/highlighter** path
(`src/compiler/10.frontend/treesitter/outline_lexer.spl` and friends) and by
`const_eval.spl`/the flat-AST bridge, not by the actual statement parser. The
parser that runs for `compile`/`native-build` uses the *separate* integer
token-kind table in `src/compiler/10.frontend/core/tokens.spl`
(`TOK_KW_CASE`, defined at `tokens.spl:385`, name lookup at `tokens.spl:246`)
via `src/compiler/10.frontend/core/lexer_struct.spl`.

Direct test against the self-hosted `bootstrap/stage3/simple` binary (built
from this `.spl` frontend, not the Rust seed) with the exact repro from the
2026-08-08 note:

```simple
fn main():
    var t = 0
    for case in [1, 2, 3]:
        t = t + case
    print "sum={t}"
main()
```

```
$ bootstrap/stage3/simple compile case_repro.spl --format=smf
[ERROR] MIR error: MIR lowering error: unsupported MIR type kind [wildcard-arm] disc=-1: <value:0x4>
```

No parse error — `case` is accepted as the loop-binding identifier. The MIR
error is a **pre-existing, unrelated** defect: swapping the binding name to
plain `x` (`for x in [1, 2, 3]: t = t + x`) reproduces the *identical* error
message and disc value, proving it's a `for`-over-array-literal MIR-lowering
gap (an unhandled `HirTypeKind` arm in
`src/compiler/50.mir/_MirLowering/function_lowering.spl:805`, a generic
catch-all `case _:` fallback, not anything specific to the text "case"), not
a keyword-scoping issue. That MIR gap is out of scope for this bug and not
further investigated here.

Why the parser already accepts it: `parse_for_binding_name()`
(`src/compiler/10.frontend/core/parser_stmts.spl:1152-1169`) has a
soft-keyword fallback —

```
val kind_name = tok_kind_name(par_kind_get())
if keyword_lookup(kind_name) == par_kind_get():
    parser_advance()
    return kind_name
```

— which accepts *any* keyword token as a for-loop binding name and uses its
canonical spelling as the identifier text. This same pattern (`*_is_kw =
keyword_lookup(...) == par_kind_get()`) is already used at several other
binding sites in `parser_stmts.spl` (`val`/`var` decl names at lines 908 and
975, type-decl variant names at 1850/1866/1893/1909) and in
`parser_expr.spl`/`parser_identifiers.spl`/`parser_decls_use.spl` for member
and segment names. So the pure-Simple frontend's keyword-as-identifier
mechanism for `case` in binding position is not merely fixable — **it is
already implemented and working**, and needs no change.

**Corrected scope:** this bug is confined entirely to the Rust seed's lexer,
which hard-reserves `case` unconditionally with no contextual exception:

```
src/compiler_rust/parser/src/lexer/identifiers.rs:138:    "case" => TokenKind::Case,
```

Per the task boundary (`src/compiler_rust/**` is off-limits to edit), this is
**ARCHITECTURAL-OPEN**: the fix is a one-line-looking change in the seed
lexer/parser to make `Case` a soft/contextual keyword like the `.spl`
frontend already does, but making that change safely (i.e. auditing every
place the seed parser currently assumes `Case` can't appear as a plain
identifier token, and updating the seed's own match-arm/pattern parsing to
disambiguate) is Rust-seed parser work outside this task's remit. No fix is
landed for the seed; the standalone repro above and the file:line citations
are the verification evidence. The pure-Simple side required no change
because it was never actually broken — only mis-diagnosed as broken by an
unverified grep-only claim in the 2026-08-08 note.
