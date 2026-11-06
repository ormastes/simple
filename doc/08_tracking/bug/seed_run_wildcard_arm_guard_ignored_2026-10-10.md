# Seed `simple run` ignores a guard on a wildcard arm (`case _ if c:`); `simple test` does not

Status: FIXED 2026-11-06 (branch `work/seed-jit-batch3-20261106`).
Severity: P3 (the seed `run` engine only; the seed spec
interpreter used by `simple test` and the pure-Simple MIR lowering are both
correct). Found 2026-10-10 (robustness item 3a); scope corrected 2026-10-11
after review: an earlier version of this record blamed the seed interpreter
as a whole, which was wrong.

## Resolution (2026-11-06)

Root cause: the seed HIR match lowering short-circuited every bare `_` arm to
its body without consulting `arm.guard`, in BOTH match chains:

- statement position: `src/compiler_rust/compiler/src/hir/lower/stmt_lowering.rs`
  `lower_match_arms_stmt` (~2912);
- expression position (the function-tail `match` in the repro):
  `src/compiler_rust/compiler/src/hir/lower/expr/control.rs`
  `lower_match_arms` (~556).

So `case _ if c:` lowered as `case _:` and every later arm was dropped. Both
shortcuts now fire only when `arm.guard.is_none()`; a guarded wildcard takes
the normal path (wildcard condition `true`, then `lower_match_guard`).

Evidence (debug seed built from `release/1.0.0` @ `a58d06d80d3`, repro
`test/fixtures/seed_interp/wildcard_arm_guard_repro.spl`):

| lane | before | after |
|---|---|---|
| `SIMPLE_EXECUTION_MODE=jit` | `d1 3 3` / `d2 3 4` / `d3 3 3` | `d1 3 4` / `d2 3 4` / `d3 3 4` |
| default `run` | `d1 3 3` / `d2 3 4` / `d3 3 3` | `d1 3 4` / `d2 3 4` / `d3 3 4` |
| `SIMPLE_EXECUTION_MODE=interpret` | `d1 3 4` / `d2 3 4` / `d3 3 4` | unchanged |

Rust tests `compiler/tests/wildcard_arm_guard_jit.rs`
(`guarded_wildcard_arm_in_value_match_falls_through_when_false`: 3333 before,
3434 after; `guarded_wildcard_arm_in_statement_match_falls_through_when_false`:
33 before, 34 after).

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

## Localized (2026-11-06) — HIR lowering, not the interpreter

Re-measured on a seed built from `release/1.0.0` @ `ecb705896a4` with
`test/fixtures/seed_interp/wildcard_arm_guard_repro.spl`:

| lane | output |
|---|---|
| `SIMPLE_EXECUTION_MODE=interpret` | `d1 3 4` / `d2 3 4` / `d3 3 4` (correct) |
| `SIMPLE_EXECUTION_MODE=jit` | `d1 3 3` / `d2 3 4` / `d3 3 3` |
| default `run` | `d1 3 3` / `d2 3 4` / `d3 3 3` |

The tree-walk interpreter is correct. The defect is in the seed's HIR
lowering of statement-position `match`:
`src/compiler_rust/compiler/src/hir/lower/stmt_lowering.rs` ~2912,
`lower_match_arms_stmt`, short-circuits `Pattern::Wildcard` to its body
(`return self.lower_block(&arm.body, ctx)`) without consulting `arm.guard`,
so `case _ if c:` behaves as `case _:` and every later arm is dropped. A
binding arm (`case x if c:`) takes the normal path through
`lower_match_guard`, which is why `d2` is correct. Fix direction: take the
shortcut only when `arm.guard.is_none()`; a guarded wildcard should lower
through `lower_match_guard` with a constant-true pattern condition.
Owner: seed HIR/JIT lane (`hir/lower/**`), not the interpreter lane.
