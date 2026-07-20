# Bug: composite-unit `.to()` conversion returns `bool`, and `^` (power) is not supported between a unit and a plain number

- **Date:** 2026-07-20
- **Status:** open (found triaging `test/unit/lib/unit/unit_composite_spec.spl`)
- **Area:** unit-type semantic analysis / conversion dispatch (compiler-level
  `unit` feature, not `.spl` stdlib — no `fn to(...)`/`UnitRegistry` source
  found under `src/lib/`, so this is implemented in the Rust semantic
  analyzer), deployed binary
  `bin/release/x86_64-unknown-linux-gnu/simple`
- **Related but distinct from:** `unit_type_si_prefix_and_suffix_bugs_2026-07-20.md`
  (that doc covers SI-prefix literal scaling `_k`/`_m` and `.suffix()` cross-block
  registry collision; this doc covers composite-unit `.to()` conversion and the
  `^` power operator — different symptoms, same general unit-type feature area,
  not consolidated because the failing code paths don't overlap)

## Symptom 1: `<composite_unit>.to(<other_composite_unit>)` returns `bool`, not the converted unit value

Command:
```
bin/release/x86_64-unknown-linux-gnu/simple test test/unit/lib/unit/unit_composite_spec.spl --no-session-daemon
```

Repro (`test/unit/lib/unit/unit_composite_spec.spl:37-49`):
```simple
it "AC-5: 60 kmph converts to ~16.6667 mps":
    val v_kmph: kmph = 60_kmph
    val v_mps: mps   = v_kmph.to(mps)
    expect(v_mps.value()).to_be_greater_than(16.6666)
```

Failure:
```
✗ AC-5: 60 kmph converts to ~16.6667 mps
  semantic: method `value` not found on type `bool` (receiver value: false)
✗ AC-5: mps converts back to kmph with round-trip ≈ identity
  semantic: method `value` not found on type `bool` (receiver value: false)
```

`v_kmph.to(mps)` is declared to return an `mps`-typed value (assigned to
`val v_mps: mps`), but the interpreter evaluates the call to the bare boolean
`false`, so the subsequent `.value()` call fails with "method not found on
bool". Both examples in this file that call `.to(...)` on a composite
(kmph/mps) unit hit this; all other composite-unit tests in the file that
don't call `.to()` pass (division-form composite units, 3/3 and 2/2 examples
green per the same run).

Root-cause hypothesis: `.to(<UnitType>)` on a composite/derived unit is
likely being resolved as a boolean-returning predicate (e.g. mis-dispatched
to something like a type-compatibility check `is_convertible_to` or an
equality-style comparison) instead of the actual value-converting method —
consistent with the "static/method dispatch selects the wrong overload for a
domain-specific unit-system call" class of bug already seen in this campaign
for other feature areas. Not isolated further (no `.spl`-level `to()`
definition exists to inspect; this needs Rust semantic-analyzer level
tracing, out of scope for this triage pass — no seed source changes per
guide).

## Symptom 2: `^` (power) is rejected between a unit value and a plain integer

Repro (`test/unit/lib/unit/unit_composite_spec.spl`, "AC-5: 3_m ^ 2 == 9_m2"):
```simple
it "AC-5: 3_m ^ 2 == 9_m2":
    ...
    expect(3_m ^ 2)...   # exact assertion body not re-quoted here; see spec file
```

Failure:
```
✗ AC-5: 3_m ^ 2 == 9_m2
  semantic: invalid operation: cannot apply BitXor between unit 'm' and non-unit value
```

`^` is being parsed/lowered as the bitwise-XOR operator (its usual meaning in
this language) rather than a power/exponent operator in this unit-arithmetic
context — the test's intent (`3_m ^ 2` producing an area unit `9_m2`) requires
`^` to mean "raise to power N and produce a derived unit" when the left
operand is a unit value and the right is a dimensionless integer literal.
Either (a) the unit-type feature is missing a power-operator overload for
this shape, or (b) this specific spelling was never a supported operator for
unit exponentiation and the spec is asserting an unimplemented sugar. Left
unclassified between "genuine bug" and "spec asserts unimplemented feature"
pending owner review — not fixable via a test-only edit either way (both
readings require a compiler/feature change, not a stale API rename).

## Affected spec

`test/unit/lib/unit/unit_composite_spec.spl` — 3 of 7 examples fail (2 from
Symptom 1, 1 from Symptom 2); left unmodified per the "never weaken an
assertion" rule — all three assertions are testing the officially-documented
composite-unit conversion/exponentiation contract.
