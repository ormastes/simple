# Seed interpreter ignores a guard on a wildcard arm (`case _ if c:`)

Status: OPEN. Severity: P2 (wrong result in the oracle/test runner; the
pure-Simple MIR lowering is correct). Found 2026-10-10 by the match guard
parity spec (robustness item 3a).

## Reproduce

Seed `C:/dev/simple-bootstrap-storage/seed-head/simple.exe run`:

```simple
enum E:
    A
    B

fn d1(n: i64, c: bool) -> i64:
    match n:
        case 1:
            1
        case _ if c:
            3
        case _:
            4

fn d2(n: i64, c: bool) -> i64:
    match n:
        case 1:
            1
        case x if c:
            3
        case _:
            4

fn d3(e: E, c: bool) -> i64:
    match e:
        case E.A:
            1
        case _ if c:
            3
        case _:
            4

fn main():
    print "d1 {d1(5, true)} {d1(5, false)}"
    print "d2 {d2(5, true)} {d2(5, false)}"
    print "d3 {d3(E.B, true)} {d3(E.B, false)}"
```

Observed: `d1 3 3`, `d2 3 4`, `d3 3 3`. Expected: `d1 3 4`, `d2 3 4`, `d3 3 4`.

The guard on `case _ if c:` is not evaluated: the arm is taken with
`c == false`, for both an int and an enum scrutinee. The same guard on a
binding arm (`case x if c:`) is evaluated correctly, so the defect is specific
to the wildcard pattern. Not localized further (seed parser vs seed
interpreter); the pure-Simple frontend parses the guard (`has_guard` is set and
the MIR carries the branch).

## Consequences

- The seed is not a valid oracle for this one arm shape.
  `test/01_unit/compiler/50.mir/match_guard/match_guard_parity_spec.spl` asserts
  that shape against the language rule (134) and does not compare it with the
  seed (which returns 133).
- Any spec or compiler module executed by the seed that relies on a guarded
  `case _ if ...:` takes the arm unconditionally.

## Fix

In the Rust seed (bootstrap-only). Not attempted here: the seed binary used by
the lanes is a pinned artifact.
