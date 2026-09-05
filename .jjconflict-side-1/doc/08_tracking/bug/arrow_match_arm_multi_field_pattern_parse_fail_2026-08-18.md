# Arrow-form `match` arm fails to parse when the pattern binds 2+ fields

- **Filed:** 2026-08-18
- **Lane:** RUNFIX (doctest/Markdown fence tests)
- **Status:** OPEN — doctest deliberately left RED (evidence, do not "fix" the doc)
- **Found by:** `bin/simple test README.md --sdoctest --no-db --mode=interpreter`
  fails at block line 594; the failing code is hoisted from the `fn perimeter`
  example at `README.md:448-453`.

## Symptom

The short arrow form `| Pattern -> expr` parses correctly only when the enum
pattern binds **at most one** field. With two or more bindings the parser
mis-reads the arm body.

```simple
enum Shape:
    Circle(r: f64)
    Rectangle(w: f64, h: f64)

fn perimeter(s: Shape) -> f64:
    match s:
        | Circle(r) -> 2.0 * r            # OK
        | Rectangle(w, h) -> 2.0 * (w + h)  # parse error
```

Errors observed (Rust seed `bin/release/x86_64-unknown-linux-gnu/simple`):

- body `2.0 * (w + h)` -> `Unexpected token: expected identifier, found Float(2.0)`
- body `w + h`         -> `Unexpected token: expected LParen, found Plus`

The second message is the tell: after a multi-binding pattern the parser is
still in *pattern* position and wants another parenthesised group, i.e. the
`->` is not terminating the pattern.

## Not a documentation error

- Single-binding arrow arms parse fine (`| Circle(r) -> 2.0 * (r + 1.0)` => `4.0`).
- The equivalent `case` block form with the same 2-field pattern works:
  `case Rectangle(w, h): w + h` => `5.0`.

So the README example is written in documented, intended syntax and the
compiler is wrong. Per lane policy the doctest is **left failing** rather than
rewritten into the `case` form — rewriting it would delete the evidence.

## Repro

```
enum Shape:
    Rectangle(w: f64, h: f64)
fn perimeter(s: Shape) -> f64:
    match s:
        | Rectangle(w, h) -> w + h
print perimeter(Shape.Rectangle(2.0, 3.0))
```

Expected `5.0`; actual: parse error at the `+`.

## Fix location (not attempted here)

Match-arm parsing in the compiler front end — the arrow-arm path needs the same
multi-field destructuring pattern parser the `case` path already uses.
