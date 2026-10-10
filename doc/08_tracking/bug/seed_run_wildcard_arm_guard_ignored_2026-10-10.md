# Seed `simple run` ignores a guard on a wildcard arm (`case _ if c:`); `simple test` does not

Status: OPEN. Severity: P3 (the seed `run` engine only; the seed spec
interpreter used by `simple test` and the pure-Simple MIR lowering are both
correct). Found 2026-10-10 (robustness item 3a); scope corrected 2026-10-11
after review: an earlier version of this record blamed the seed interpreter
as a whole, which was wrong.

## Reproduce

`C:/dev/simple-bootstrap-storage/seed-head/simple.exe run file.spl`:

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

Observed with `simple run`: `d1 3 3`, `d2 3 4`, `d3 3 3`. Expected: `d1 3 4`,
`d2 3 4`, `d3 3 4` (re-measured 2026-10-11).

The same functions inside a spec executed with `simple test` return the
expected values (`w(5, true) = 3`, `w(5, false) = 4`), and
`test/01_unit/compiler/50.mir/match_guard/match_guard_parity_spec.spl` asserts
the wildcard-guard shape against that oracle (134) like every other shape.

So the defect is in the engine `simple run` selects (it logs
`[engine-demotion] reason=hybrid-interp-splice`), not in the seed's spec
interpreter. Not localized further. The guard on a binding arm (`case x if
c:`) is evaluated correctly on both paths.

## Fix

In the Rust seed (bootstrap-only). Not attempted here.
