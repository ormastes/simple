# BUG: README documents `| Pattern -> expr` match arms as "preferred", and the parser rejects them

- **id:** readme_arrow_match_arm_syntax_does_not_parse_2026-09-19
- **status:** OPEN — recorded, deliberately not "fixed" by editing the README (see Why below)
- **severity:** P2 — a documented language form that does not exist; the only failing block in README.md's executable test surface
- **found:** 2026-09-19, by running the markdown doctest surface (`bin/simple test README.md`)

## Symptom

`README.md` presents an arrow form of `match` and calls it preferred:

```simple
# Preferred arrow syntax (shorter)
fn perimeter(s: Shape) -> f64:
    match s:
        | Circle(r) -> 2.0 * 3.14159 * r
        | Rectangle(w, h) -> 2.0 * (w + h)
        | Square(side) -> 4.0 * side
        | Triangle(a, b, c) -> a + b + c
```

It does not parse:

```
parse: Unexpected token: expected identifier, found Float(4.0)
```

Minimal repro — the `case` form above it compiles and runs; only the arrow form fails:

```simple
enum Shape:
    Circle(f64)
    Square(f64)

fn area_case(s: Shape) -> f64:          # parses, runs, returns 3.14159
    match s:
        case Circle(r):
            3.14159 * r * r
        case Square(side):
            side * side

fn area_arrow(s: Shape) -> f64:         # parse error
    match s:
        | Circle(r) -> 2.0 * 3.14159 * r
        | Square(side) -> 4.0 * side
```

The diagnostic points at the reason: after `->` the parser expects a **type
identifier**, as in a function signature's `-> f64`, not an expression. The
first arm is consumed as something signature-shaped and the failure surfaces on
the second arm's literal.

## How it was found, and what that says about the md test surface

This is the **only** failing block in README.md's doctest run:

```
SDoctest Results: 19 total, 18 passed, 1 failed, 0 skipped, 0 errors
```

Worth recording, because the markdown doctest lane is otherwise almost unused:
`config/sdoctest.sdn` puts `README.md`, `CLAUDE.md`, `doc/`, `examples/` and
`.claude/skills/` in scope — **1,632 fences across 299 files** — yet the full
test manifest registered `sdoctest_count=1`, and that one entry is
`test/01_unit/app/simple_lab/fixtures/hello_sdoctest.md`, a fixture that is not
in the configured scope at all.

The mechanism is in `discover_sdoctest_files`
(`src/lib/nogc_sync_mut/test_runner/sdoctest/discovery.spl:16`): when a CLI path
is given it discovers from **that path** and the configured sources are never
walked. So `bin/simple test test/01_unit` finds only markdown that happens to
live under `test/01_unit`, and the configured md corpus runs only when the path
argument points at it. Pointing it at `README.md` directly is what surfaced this
defect — 19 blocks executed where the scoped runs had executed none.

## Why this is recorded rather than "fixed" in the README

Deleting or rewriting the arrow example would make the test green while removing
the only evidence that the language is missing a form its own README calls
preferred. CLAUDE.md is explicit about this case:

> When a short, safe grammar or compact expression form fails, compiles too
> slowly, or forces a workaround, fix it or record a concrete bug/feature
> request instead of silently normalizing the workaround.

So the two honest options are to implement arrow match arms in the parser, or to
record the gap. Implementing new surface syntax is a feature change, not a
defect fix, and is not something to undertake unprompted inside a test-triage
pass — hence this record.

**Whoever picks this up decides one thing first:** is `| pattern -> expr`
intended to exist? If yes, the fix is in the match-arm parser (it must accept an
expression after `->`, not a type). If no, the README section must go, and this
record is the justification for removing it rather than a silent edit.

## Related

- `rt_file_stat_returns_size_on_interpret_lane_2026-09-19` — found in the same
  pass, also by exercising a surface nothing routinely runs.
