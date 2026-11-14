# Coverage: hits inside a closure body are filed under the invoker's module (2026-11-14)

**Status:** OPEN (collector, attribution). **Area:** seed coverage collector,
`src/compiler_rust/compiler/src/interpreter/coverage_helpers.rs`
(`current_coverage_file`, used by `span_to_location` and `record_decision_site`).
**Found:** while fixing
`coverage_value_match_arm_tail_and_lambda_body_unrecorded_2026-11-14.md`.

## Symptom

`current_coverage_file` reads `CURRENT_EXEC_MODULE`, and a closure body inherits that
from whoever invokes it. A lambda written in module A and invoked by a function of
module B therefore records under B's file, at A's line numbers:

- line hits taken through `exec_node` inside the closure (statements of a
  value-position `match` arm, of a `with` body, of an `if`-expression block);
- every decision row of the closure's `if` / `while` / guard sites. The static
  registration (`coverage_sites.rs`) files the site under A, so A keeps a never-visited
  `0, 0` row and B gains a row for a line it may not have.

This is the flattering direction for B: a line B never ran reads as hit.

## Repro (seed built from this change's base, `6a71372cabc`)

`covhelper_mod.spl` (5 lines):

```
pub fn covhelper_apply(f: fn(i64) -> i64, x: i64) -> i64:
    val before = x + 1
    val r = f(before)
    r
```

`main2.spl`, run with `SIMPLE_COVERAGE=1`:

```
use covhelper_mod.{covhelper_apply}

fn probe_cross(n: i64) -> i64:
    val f = \x:
        val r = match x:
            case 2:
                val inner = x * 10
                if inner > 5:
                    inner
                else:
                    0
            case _:
                1
        r
    covhelper_apply(f, n)

fn main():
    print probe_cross(1)
```

Artifact: `covhelper_mod.spl, 7, 1` (line 7 is `val inner` in `main2.spl`; the helper
has 5 lines) and decision rows `covhelper_mod.spl, 8, 17, 1, 0` beside
`main2.spl, 8, 17, 0, 0`.

## Not changed by the fix above

That fix records closure-body statements and value-`match` arm tails under the module
that WROTE the code (`record_node_coverage_lexical`, via `private_call_caller`), so
its new records are filed correctly. The `exec_node` records and the decision probes
shown here still use `current_coverage_file`.

## Fix direction

Make `current_coverage_file` prefer the lexical owner (`TOP_LEVEL_MODULE`, the value
`private_call_caller` returns first) whenever one is set. That also moves an imported
module's top-level hits from the entry file to the module's own file, which changes
`toplevel_excluded` assumptions in `coverage_module_report.spl` and the RESIDUAL note in
`test_runner_single.spl`; it needs its own before/after on decision figures, because
decision ids hash the file. The if-expression anchor (`fn_anchor`) is inherited from
the invoker in the same way and needs the same treatment.

## Status after the arm-tail / lambda-body fix (2026-11-14)

Still OPEN; not fixed by that change. It does not block any figure there:
`enum_constructor_payload.spl` reads 100.0% (231/231) lines on both the base and the
fixed seed. The block-closure executors never delegate to `exec_node`, so a closure
statement is not recorded twice (once lexically, once under the invoker); the
remaining misattribution is limited to the `exec_node` records and decision rows
listed above.
