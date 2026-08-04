# `case Point { x: 0, y: b }:` — named-field struct patterns were unreachable

**Status:** FIXED 2026-08-04 (two defects: parser, then binder).
**Found:** 2026-08-04, while fixing top-level struct-pattern refutability
(`class_pattern_condition`, hir/lower/expr/control.rs).
**Severity:** medium — a pattern spelling that the parser, both HIR lowering
twins, the tree-walk interpreter and the pretty printer all implement, and that
no program could actually use.

## Symptom (original)

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

## Defect 1 — the parser ate the field separator (FIXED)

`parser/src/parser_patterns.rs`. The `Name { ... }` field loop parsed each
field's sub-pattern with the FULL `parse_pattern`, which supports
comma-separated or-patterns (`case Int(_), Float(_):`). Given
`{ x: 0, y: b }`, `parse_pattern` parsed `0`, then saw the field-separating `,`
and `is_comma_or_pattern_context()` (peek == identifier `y`) said "or-pattern".
It swallowed the separator, parsed `y` as the next alternative, and left the
field colon in place — which the field loop then reported as
`expected Comma, found Colon`.

Bisection that pins it exactly (the failing rows are the ones with BOTH a `:`
sub-pattern AND a following field):

| spelling | before |
|---|---|
| `Point { x: a }` | parses |
| `Point { x }` | parses |
| `Point { x, y }` | parses |
| `Point { x: 0 }` | parses |
| `Point { x: a, y: b }` | **expected Comma, found Colon** |
| `Point { x: 0, y: 1 }` | **expected Comma, found Colon** |

Fix: `parse_pattern_no_comma_or` — `parse_pattern_inner(allow_comma_or: false)`.
`|` or-patterns still work inside a field; only the comma form is suppressed,
because there the comma delimits FIELDS. This is the same reasoning
`parse_enum_payload_patterns` already applied ("Use parse_single_pattern to
avoid comma being consumed as or-pattern") — the brace form had been missed.

## Defect 2 — no binder for a top-level `Pattern::Struct` (FIXED)

Revealed only once defect 1 was fixed, and invisible to the interpreter:

```
              interpreter   JIT (before)
d1_named_hit      7            0
d1_named_miss   107          100
d1_named_short    7            0
```

The CONDITION half was already correct (`named_struct_pattern_condition`
selects the right arm — `miss` took arm 2, so `+100` was applied). The BINDER
half did not exist: `build_pattern_binding_stmts` (hir/lower/stmt_lowering.rs)
had arms for `Identifier`, `Tuple`/`Array` and `Enum`, but **none for
`Pattern::Struct`**, so every name was read off the zeroed stack — the classic
"right arm, zero values" signature. The tree-walk interpreter recurses in
`interpreter_patterns.rs` and was always right, so an interpreter-only run
could not see this.

Fix: a `Pattern::Struct` arm in `build_pattern_binding_stmts` that resolves each
field NAME to its declaration index via `struct_field_list` and then calls
`bind_struct_fields` positionally — identical to what `bind_subpattern`'s
`Pattern::Struct` arm already did for the NESTED position, and to what
`named_struct_pattern_condition` does for the refutability half.

## Coverage

`test/fixtures/compiler/top_level_struct_subpattern_matrix.spl`, rows
`d1_named_hit` / `d1_named_miss` / `d1_named_short`, inside the `BADCOUNT`
gate (not `OPENCOUNT`). `d1_named_miss` is the row an irrefutable `Bool(true)`
condition cannot answer; `d1_named_hit` is the row a missing binder cannot
answer. Both directions are required — a positive-only test detects neither
defect.
