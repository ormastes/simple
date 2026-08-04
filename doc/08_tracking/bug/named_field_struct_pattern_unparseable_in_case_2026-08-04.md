# `case Point { x: 0, y: b }:` does not parse — named-field struct patterns are unreachable

**Status:** OPEN (parser)
**Found:** 2026-08-04, while fixing top-level struct-pattern refutability
(`class_pattern_condition`, hir/lower/expr/control.rs).
**Severity:** medium — a pattern spelling that the parser, both HIR lowering
twins, the tree-walk interpreter and the pretty printer all implement, and that
no program can actually use.

## Symptom

```
struct Point:
    x: i64
    y: i64

fn f(p: Point) -> i64:
    match p:
        case Point { x: a, y: b }: a + b
        case _: -1
```

```
$ simple run t.spl
error: compile failed: parse: in "t.spl": Unexpected token: expected Comma, found Colon
```

Both engines, both the literal form (`{ x: 0, y: b }`) and the pure-binder form
(`{ x: a, y: b }`). The positional spelling `case Point(a, b):` parses and runs
fine, so the gap is specific to the brace form in `case` position.

## Why it is not a lowering bug

`Pattern::Struct { name, fields }` is fully implemented everywhere downstream:

| consumer | file |
|---|---|
| statement-form condition | `hir/lower/stmt_lowering.rs` `lower_pattern_condition_stmt` |
| expression-form condition | `hir/lower/expr/control.rs` `lower_pattern_condition` |
| sub-pattern condition | `hir/lower/expr/control.rs` `subpattern_condition` |
| binder | `hir/lower/stmt_lowering.rs` `bind_subpattern` |
| tree-walk interpreter | `interpreter_patterns.rs:411` |
| pretty printer | `pretty_printer.rs:933` |

and the only PRODUCER is `parser/src/parser_patterns.rs:313`, in the
`TokenKind::Identifier` arm, guarded by `if self.check(&TokenKind::LBrace)`.
That arm's own loop reads correctly (`ident`, optional `: pattern`,
`,`-separated, `}`-terminated), so the failure is upstream of it: the `case`
arm parser does not reach `parse_pattern` with the `{` still available — the
brace is consumed or re-interpreted (block / struct-literal ambiguity) before
the pattern parser sees it. Root cause not isolated; the reproduction above is
the whole of what is measured.

## Consequence for the struct-pattern refutability fix

`class_pattern_condition` (positional spelling) and
`named_struct_pattern_condition` (this spelling) were both wrong in the same
way — an unconditional `Bool(true)` that discarded every field sub-pattern —
and both are fixed. Only the positional one is covered by
`test/fixtures/compiler/top_level_struct_subpattern_matrix.spl`, because no
executable row can be written for a pattern that cannot be parsed. Add the
`d1_named_hit` / `d1_named_miss` rows to that matrix the day this parses.

## Repro

Minimal file is the `fn f` above; any `case Name { ... }:` reproduces.
