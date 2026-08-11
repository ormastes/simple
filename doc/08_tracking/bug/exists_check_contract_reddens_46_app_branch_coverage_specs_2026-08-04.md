# App-scope blast radius of the `T?`-into-`bool`-parameter defect: 46 branch-coverage specs

**Status:** ALREADY-FIXED, re-verified 2026-08-10 — the root cause (seed
`coerce_param` had no bool arm, `src/compiler_rust/compiler/src/interpreter_call/core/arg_binding.rs`)
was fixed upstream (`present_value_as_bool_arg`, landed by commit
`aff29a24dfe`, 2026-08-08). Fresh run: `bin/simple test
test/01_unit/app/branch_coverage_1_spec.spl --no-cache --no-cover-check` →
`Results: 78 total, 78 passed, 0 failed` (previously 75/78, 3 red). The
138-example blast radius recorded below is resolved by that same upstream fix.
**Found:** 2026-08-04
**Severity:** high — largest single failure cluster under `test/*/app/` (historical, now resolved)
**This file is a blast-radius record, not a second root cause.**

## Root cause — already filed elsewhere, do not fix here

A parallel lane proved the mechanism: a `T?` value bound to a `bool` parameter is
**neither presence-coerced nor rejected** — the seed's `coerce_param`
(`arg_binding.rs:84`) has no bool arm, so the Option payload is passed straight
through. That lane owns the fix. See also, for the contract question underneath
it:

- `doc/08_tracking/bug/bool_typed_parameter_accepts_non_bool_and_jit_corrupts_it_2026-08-04.md`
- `doc/08_tracking/bug/exists_operator_returns_payload_not_bool_2026-08-04.md`
- `doc/08_tracking/bug/exists_check_on_optional_i64_returns_payload_2026-08-01.md`
- `doc/08_tracking/bug/mirror_both_red_defect_families_2026-07-30.md` (Family A)

This file exists only so the 138 red examples below are not re-triaged as
independent app defects.

## Symptom in this scope

```sh
SIMPLE_TIMEOUT_SECONDS=0 bin/simple test test/01_unit/app/branch_coverage_1_spec.spl \
  --no-cache --no-cover-check
```

Actual (`Results: 78 total, 75 passed, 3 failed`):

```
  ✗ dict get - exists          expected value to equal true
  ✗ option is some             expected 42 to equal true
  ✗ option chain - some/some   expected 10 to equal true
```

Expected: 78 passed.

The bodies (`test/01_unit/app/branch_coverage_1_spec.spl:408-432`) are the exact
shape the sibling lane describes — a `T?` handed to a `bool` parameter:

```simple
fn check(condition: bool):
    expect(condition).to_equal(true)

it "dict get - exists":       check(d.get("key").?)      # gets "value"
it "option is some":          check(Some(42).?)          # gets 42
it "option chain - some/some": check(Some(Some(10)).?)   # gets 10
```

The mirrored negative cases in the same file (`check(not d.get("missing").?)`,
`check(not opt.?)` with `opt = nil`) pass, because `not nil` is `true` — which is
why the split is exactly 3 per file and never 6.

## Blast radius (measured 2026-08-04)

| Directory | branch_coverage files | red | examples lost |
|---|---|---|---|
| `test/01_unit/app/` | 25 | 24 (all but `_3`) | 72 |
| `test/unit/app/` (legacy duplicate) | 25 | 22 | 66 |

The two trees are byte-identical (`diff -q test/unit/app/branch_coverage_1_spec.spl
test/01_unit/app/branch_coverage_1_spec.spl` → identical), so the same three
assertions are counted twice. **138 failing examples from one defect.** A further
79 spec files under `test/01_unit/app`, `test/unit/app`, `test/02_integration/app`
and `test/03_system/app` contain a `check(<expr>.?)` call and are exposed to the
same fix.

## Why not fixed in this lane

The fix is in the seed's parameter binding, which another lane already owns;
touching it from here would collide. Rewriting the 138 assertions to
`check(x.? != nil)` instead would bake the *unsettled* reading of `.?` into the
corpus — precisely what the 2026-08-01 bug asks not to happen ("the lowering of
`.?` needs a single documented contract and a spec that gates it"). No spec was
touched.
