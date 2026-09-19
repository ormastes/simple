# Feature request: string-interpolation holes should be real child expressions

**Status:** OPEN 2026-09-19 — filed from a lint/auto-fix correctness incident,
but the request is not lint-specific.
**Area:** `src/compiler/10.frontend/core/` (parser + `_AstExpr` arena)
**Raised by:** `doc/08_tracking/bug/coll_certain_fix_textual_proofs_disagree_with_parser_2026-09-19.md`

## What the AST does today

`val t = "{x.len()}"` parses to a plain **`EXPR_STRING_LIT`** whose text is the
literal `{x.len()}`, with **zero child expressions**. Measured by dumping the
arena (2026-09-19): `expr_child_exprs` returns nothing, `expr_get_str` returns
the source text of the hole, and the tag is `EXPR_STRING_LIT` — not
`EXPR_INTERPOLATED_STRING`, which exists but is not what the parser produces
here. The hole is lowered to concatenation later in the pipeline.

By contrast `print(x.len())` is an ordinary `EXPR_CALL` and walks normally.

## Why that is a problem for every analysis, not just one

Any pass that answers a question of the form "does this function do X to `y`"
by walking the AST is blind to everything inside `"{...}"`. That is not a
missing feature of one lint; it is a hole in the tree that every consumer
inherits:

- **The COLL Certain auto-fix** shipped a rewrite that silently changed
  program output, because `print "{seen.pop()}"` mutated the array it was
  reasoning about and nothing in the AST said so. Measured: `[1,3]` became
  `[3]`; the COLL002 sibling turned `[1,2]` into `[1,2,2]`.
- **Unused-variable / dead-binding analysis** must over-report or under-report
  a name used only inside a hole.
- **Effect, capability and borrow analysis** cannot see a call made from a
  hole.
- **Rename / go-to-definition** in the LSP cannot resolve an identifier in a
  hole without re-lexing the literal.
- **COLL022** (`sort` then `take`) already documents this exact blindness as a
  known limit and has to stay silent whenever a hole is in scope, because a
  use it cannot see would invert its answer.

Every one of those consumers is today obliged to invent its own text scan of
the literal, which is precisely the class of "second opinion computed from
characters" that caused sixteen wrong rewrites in the incident above.

## Requested change

Parse an interpolated string into a node whose holes are ordinary child
expressions — `EXPR_INTERPOLATED_STRING` already exists and `expr_child_exprs`
already yields `expr_get_args` for it, so the arena contract needs no change;
the parser needs to build it. Concretely:

1. `"a{e1}b{e2}"` yields `EXPR_INTERPOLATED_STRING` with the hole expressions
   as args, each carrying its own span pointing into the literal.
2. `expr_child_exprs` on that node yields exactly those hole expressions, so
   every existing generic walker picks them up with no change.
3. A literal with no holes keeps parsing as `EXPR_STRING_LIT`.

## Acceptance

- Dumping the arena for `val t = "{x.len()}"` shows a node with one child
  expression that is a method call on `x`.
- The interim rule in `collection_patterns.spl`
  (`literal_hole_mentions`, a bare-token text scan of the literal) can be
  deleted, and `collection_certain_fix_safety_spec`'s `d1`/`d1b`/`d1c`
  examples still refuse — for the right reason, through the generic walk.
- COLL022's interpolation-opacity note and its
  "stays silent when an interpolation hole could be using the sort result"
  example can be replaced by a real answer.

## Interim measure in place

`collection_patterns.spl` treats a string literal that contains `{` and
mentions the tracked name as a bare token as a USE of that name. It is
deliberately over-approximate: it costs suggestions on literals that merely
happen to contain the name, and it cannot be precise, because the information
is not in the tree.
