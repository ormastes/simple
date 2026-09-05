# Inline `| pattern -> body` match arms parse only as the LAST arm

**Status:** OPEN
**Filed:** 2026-09-05
**Affects:** BOTH the Rust seed and the Stage-2 pure-Simple compiler — this is a
parser/grammar defect, not a codegen one.
**Severity:** MEDIUM, but with a documentation multiplier: the form that does
not work is the one the quick reference calls **preferred**.

## Smallest reproducer (6 lines)

```simple
fn f(n: i64) -> text:
    match n:
        | 0 -> "zero"
        | _ -> "other"

fn main():
    print "{f(0)} {f(9)}"
```

Seed (`bin/simple run`):

```
error: compile failed: parse: Unexpected token: expected LParen, found Newline
```

Stage-2 (`./simple native-build ...`):

```
Build failed: failed to parse ... at 4:23 during discovery:
Unexpected token: expected LParen, found Newline
```

No enum is involved — plain `i64` reproduces it.

## The rule, stated precisely

An arm written as `| pattern -> <body on the same line>` parses **only if it is
the final arm**. If another `|` arm follows it, the parser treats the body as an
expression, absorbs the next `|` as a binary-or operator, consumes the following
pattern as its right operand, and then meets `->` in expression position, where
it expects a parameter list — hence `expected LParen`.

The reported column is always the END of the *second* arm, never the first,
which is why this looks at first glance like a problem with the arm that
actually parsed fine. Three shapes of the same failure, all at the second arm:

| body of arm 2 | token the parser choked on |
|---|---|
| `"green"` | `Newline` |
| `"other"` | `Newline` |
| `w * h` | `Star` |

## What DOES work

**Block form** — arrow at end of line, body indented beneath — works for every
arm:

```simple
fn f(n: i64) -> text:
    match n:
        | 0 ->
            "zero"
        | _ ->
            "other"
```
seed: prints `zero other`.

**`case` form** works fully, inline bodies and all, including enum payload
destructuring, on both the seed and Stage-2 native:

```simple
enum Shape:
    Circle(r: i64)
    Rect(w: i64, h: i64)

fn area(s: Shape) -> i64:
    match s:
        case Shape.Circle(r): 3 * r * r
        case Shape.Rect(w, h): w * h
```
Stage-2 native: `12 15` — correct.

## Why this is filed rather than worked around

`.claude/rules/` (CLAUDE.md, Critical Rules) requires that a short, safe grammar
form which fails be fixed or recorded, not silently normalised into the
workaround. The workaround here (`case`, or block bodies) is fine and is what
callers must use today, but the documentation actively steers people the other
way:

`doc/07_guide/quick_reference/syntax_quick_reference.md`
§ Pattern Matching says **"Erlang-style `| ->` is preferred (shorter)"** and then
gives three multi-arm examples — *Basic Match*, *Pattern Guards*, and the
`| ->` variants throughout — **every one of which is written in the inline form
and therefore does not parse.** The `case` examples immediately beside them all
work. Anyone following the recommended style hits this on their first match
expression.

Do not "fix" this by rewriting the guide to drop `| ->`. Either the parser
should accept an inline arm followed by another arm (the arm separator `|` at
the start of a line, at match-arm indentation, should not be reachable as a
binary operator), or the guide's recommendation should be demoted with the
limitation stated explicitly. The parser fix is the better outcome; this record
exists so the choice is made deliberately.

## Not investigated

Where in the grammar the `|` alternation/or ambiguity is resolved. The defect is
identical on the seed and on Stage-2, so it is in shared grammar rather than in
either backend.

## Usage census — the form is documented but never actually used

```
/usr/bin/grep -rn --include='*.spl' -E '^[[:space:]]+\| .+ -> [^[:space:]]' src/ \
  | grep -vc compiler_rust
0
```

**Zero** inline `| pattern -> body` match arms exist in owned Simple source
(`src/**`, excluding the vendored `src/compiler_rust/` seed tree). That is
consistent with the form having never worked: the codebase uses `case` arms and
block-form `| ->` arms throughout. The 441-hit figure a first pass produced was
an artifact of ugrep silently treating `--include=*.spl` as a path — it counted
`.md`, `.lean` and markdown tables. The corrected count is 0.

## Second, independent grammar gap found the same session: `=>` lambdas

`doc/07_guide/quick_reference/syntax_quick_reference.md:348` documents
`nums.flat_map(x => [x, x * 10])`, and the file uses `x => ...` as the explicit
lambda form. It does not parse, on **either** compiler.

Smallest reproducer (3 lines):

```simple
fn main():
    val f = x => x + 1
    print "{f(1)}"
```

Seed (`bin/simple run`):

```
error: compile failed: parse: Unexpected token: expected expression, found FatArrow
```

Stage-2 `native-build` gives the same `expected expression, found FatArrow` at
the `=>` column.

The backslash form parses on both and evaluates correctly on the seed
(`val add_k = \x: x + k` -> `add_k(5)` == 15), so `\x:` is the working spelling
today. It is recorded here rather than quietly substituted for the same reason
as the match arms: the guide recommends the form that does not work.

Note that `\x:` closures, while they parse and interpret correctly, **SEGV under
Stage-2 native codegen** — that is a separate defect, tracked as Defect 3 in
`stage2_native_codegen_silent_wrong_values_aarch64_2026-09-05.md`.
