# backend_metal_font_spec: `.?` in assertion position asserted presence, not value

- **Status:** RESOLVED (2026-09-12)
- **Severity:** P2 — a spec that silently asserted something other than what it read
- **Lane:** macOS open-bugs round 2, LANE 3 (wrong output)
- **Host:** macOS 25.5.0, Apple M4
- **Seed:** `/Users/ormastes/simple/build/cargo-r2/release/simple` (`stat -f '%z %m'` = `39528776 1789199850`)

## Symptom (reproduced before the fix)

```
SIMPLE_EXECUTION_MODE=interpreter SIMPLE_TIMEOUT_SECONDS=0 \
  <seed> run test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_font_spec.spl
```

```
  ✗ rejects destination coordinate overflow before ABI packing
    expected true to equal -2147483648
9 examples, 1 failure
SPEC FILE VERDICT: ... outcome=ERROR declared>=9 executed=9 passed=8 failed=1
```

The wrong value is the literal `true`. The oracle wanted the clamped i32 floor
`-2147483648`; the subject the matcher actually received was a boolean.

## Root cause — NOT the i32 boundary, and NOT macOS-specific

The `-2147483648` in the message is a red herring. `font_destination_origin`
(`src/lib/common/gpu/font_atlas_composite.spl:60`) is correct at every input
probed: run outside a spec it returns `Option::Some(-2147483648)` for
`(-2147483648, 0, 2)`, `Option::Some(2147483647)` for the ceiling, and
`Option::None` for each overflow case.

The defect is in the SPEC. `.?` has two readings, and the interpreter chooses by
POSITION, deliberately and documented:

- `src/compiler_rust/compiler/src/interpreter_call/bdd.rs:588-620`,
  `eval_assertion_operand` — in an `expect(...)` subject, or on either side of a
  comparison inside one, `Expr::ExistsCheck` collapses to
  `Value::Bool(!matches!(value, Value::Nil))`, the parser's documented "is
  present" contract.
- Everywhere else (a `val` binding, a condition, an interpolation) `.?` yields
  the present payload, so `if val v = opt.?:` can bind it.

So `expect(font_destination_origin(...).?).to_equal(-2147483648)` compared the
PRESENCE bool against a number. It was an assertion about presence wearing the
clothes of an assertion about value. That collapse was introduced on purpose by
`doc/08_tracking/bug/sspec_test_path_value_semantics_divergence_2026-07-20.md`;
this spec was written against the other reading.

Because the behaviour lives in the seed's BDD builtin, it reproduces on every
platform. The plan listed it as a macOS item; it is not macOS-specific.

Two things masked the size of it: all THREE of lines 111-113 were failing, but
only the last failure per example is reported
(`test_runner_reports_only_last_failure_per_example_2026-08-04`); and
`std.spec` exposes `expect(value: bool)` alongside `expect(value)`
(`src/lib/nogc_sync_mut/spec.spl:734,739`), which makes a coerced bool subject
look like a plausible overload-resolution bug. It is not — the stdlib `expect`
is not even on this path; the seed's builtin is. Editing `spec.spl` was tried
and changed nothing, which is what pointed at `bdd.rs`.

## Fix

`test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_font_spec.spl:107-125`
— bind each optional to a `val` and assert on the recovered payload with `??`,
and keep one explicit `.?` presence oracle so the contract is stated rather than
avoided. No production code changed: none was wrong.

## Evidence after the fix

```
  ✓ rejects destination coordinate overflow before ABI packing
9 examples, 0 failures
SPEC FILE VERDICT: ... outcome=OK declared>=9 executed=9 passed=9 failed=0
```

## Specs (both required by .claude/rules/testing.md)

- Reproduce: `test/01_unit/lib/common/spec/exists_check_assertion_position_spec.spl`
  — 4 examples, `4 examples, 0 failures`. Pins the collapse on the exact helper,
  and pins that presence and payload readings of ONE optional disagree.
- Generalize: `test/01_unit/lib/common/spec/exists_check_assertion_generalization_spec.spl`
  — 4 examples, `4 examples, 0 failures`. Shows the collapse is a property of
  `.?` itself across numeric and text optionals produced locally, and that
  `to_be_nil()` on the raw optional is unaffected.

## Sabotage triple (each mutation run, each observed RED, each reverted)

| # | mutation | result |
|---|---|---|
| A | font spec: `expect(floor_origin ?? 0)` → `expect(floor_origin.?)` (restore the original defect) | `9 examples, 1 failure` |
| B | reproduce spec: presence oracle `to_equal(true)` → `to_equal(false)` | `4 examples, 1 failure` |
| C | generalize spec: payload oracle `to_equal(42)` → `to_equal(43)` | `4 examples, 1 failure` |

All three restored; `git status` clean of sabotage afterwards.

## Follow-up for spec authors (not fixed here, deliberately)

`expect(<optional>.?)` with a NON-bool oracle is always this bug. The reading is
legal and the runner cannot tell the two intents apart, so it stays a review
rule rather than a hard error. Any spec matching that shape should be audited
against the two specs above.
