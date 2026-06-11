# Vhdl Constraints Specification

> 1. span: test span

<!-- sdn-diagram:id=vhdl_constraints_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vhdl_constraints_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vhdl_constraints_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vhdl_constraints_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vhdl Constraints Specification

## Scenarios

### Vhdl Constraints

#### accepts matching widths and rejects mismatched widths

1. span: test span
2. span: test span
   - Expected: errors.len() equals `1`
   - Expected: errors[0].code equals `E0700`
   - Expected: errors[0].kind equals `VhdlConstraintErrorKind.WidthMismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok_checker = VhdlConstraintChecker.create()
ok_checker.add_constraint(VhdlConstraint.WidthEqual(
    signal1: "a", signal2: "b",
    width1: 32, width2: 32,
    span: test_span()
))
expect(ok_checker.check_all().is_ok()).to_be(true)

val bad_checker = VhdlConstraintChecker.create()
bad_checker.add_constraint(VhdlConstraint.WidthEqual(
    signal1: "narrow", signal2: "wide",
    width1: 8, width2: 16,
    span: test_span()
))
val errors = bad_checker.check_all().unwrap_err()
expect(errors.len()).to_equal(1)
expect(errors[0].code).to_equal("E0700")
expect(errors[0].kind).to_equal(VhdlConstraintErrorKind.WidthMismatch)
expect(errors[0].message).to_contain("narrow")
expect(errors[0].message).to_contain("wide")
```

</details>

<details>
<summary>Advanced: checks clock domains, loops, and drivers</summary>

#### checks clock domains, loops, and drivers

1. checker register signal domain
2. checker register signal domain
3. span: test span
4. dependencies: [
5. span: test span
6. span: test span
   - Expected: errors.len() equals `3`
   - Expected: errors[0].code equals `E0710`
   - Expected: errors[0].kind equals `VhdlConstraintErrorKind.ClockDomainCrossing`
   - Expected: errors[1].code equals `E0721`
   - Expected: errors[1].kind equals `VhdlConstraintErrorKind.CombinationalLoop`
   - Expected: errors[2].code equals `E0740`
   - Expected: errors[2].kind equals `VhdlConstraintErrorKind.MultipleDrivers`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val checker = VhdlConstraintChecker.create()
checker.register_signal_domain("sig_a", "clk_100")
checker.register_signal_domain("sig_b", "clk_50")
checker.add_constraint(VhdlConstraint.SameClockDomain(
    signal1: "sig_a", signal2: "sig_b",
    span: test_span()
))
checker.add_constraint(VhdlConstraint.NoCombLoop(
    signals: ["a", "b"],
    dependencies: [("a", "b"), ("b", "a")],
    span: test_span()
))
checker.add_constraint(VhdlConstraint.SingleDriver(
    signal: "shared",
    drivers: ["drv0", "drv1"],
    span: test_span()
))

val errors = checker.check_all().unwrap_err()

expect(errors.len()).to_equal(3)
expect(errors[0].code).to_equal("E0710")
expect(errors[0].kind).to_equal(VhdlConstraintErrorKind.ClockDomainCrossing)
expect(errors[0].message).to_contain("source 'sig_a'")
expect(errors[0].message).to_contain("domain 'clk_100'")
expect(errors[0].message).to_contain("destination 'sig_b'")
expect(errors[0].message).to_contain("domain 'clk_50'")
expect(errors[1].code).to_equal("E0721")
expect(errors[1].kind).to_equal(VhdlConstraintErrorKind.CombinationalLoop)
expect(errors[2].code).to_equal("E0740")
expect(errors[2].kind).to_equal(VhdlConstraintErrorKind.MultipleDrivers)
```

</details>


</details>

#### diagnoses implicit crossings with registered source and destination domains

1. checker register signal domain
2. checker register signal domain
3. checker add implicit cross domain constraint
   - Expected: errors.len() equals `1`
   - Expected: errors[0].code equals `E0710`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val checker = VhdlConstraintChecker.create()
checker.register_clock_domain(VhdlClockDomain(
    name: "core-domain",
    clock_signal: "clk_core",
    reset_signal: nil,
    reset_polarity: VhdlResetPolarity.ActiveLow,
    reset_synchrony: VhdlResetSynchrony.None_,
    edge: VhdlClockEdge.Rising
))
checker.register_clock_domain(VhdlClockDomain(
    name: "io.domain",
    clock_signal: "clk_io",
    reset_signal: nil,
    reset_polarity: VhdlResetPolarity.ActiveLow,
    reset_synchrony: VhdlResetSynchrony.None_,
    edge: VhdlClockEdge.Rising
))
checker.register_signal_domain("rx_data", "core-domain")
checker.register_signal_domain("tx_data", "io.domain")
checker.add_implicit_cross_domain_constraint("rx_data", "tx_data", test_span())

val errors = checker.check_all().unwrap_err()

expect(errors.len()).to_equal(1)
expect(errors[0].code).to_equal("E0710")
expect(errors[0].message).to_contain("source 'rx_data' in domain 'core-domain'")
expect(errors[0].message).to_contain("destination 'tx_data' in domain 'io.domain'")
```

</details>

#### diagnoses duplicate sanitized clock domain names

<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val checker = VhdlConstraintChecker.create()
checker.register_clock_domain(VhdlClockDomain(
    name: "bus-domain",
    clock_signal: "clk_a",
    reset_signal: nil,
    reset_polarity: VhdlResetPolarity.ActiveLow,
    reset_synchrony: VhdlResetSynchrony.None_,
    edge: VhdlClockEdge.Rising
))
checker.register_clock_domain(VhdlClockDomain(
    name: "bus.domain",
    clock_signal: "clk_b",
    reset_signal: nil,
    reset_polarity: VhdlResetPolarity.ActiveLow,
    reset_synchrony: VhdlResetSynchrony.None_,
    edge: VhdlClockEdge.Rising
))

val errors = checker.check_all().unwrap_err()

expect(errors.len()).to_equal(1)
expect(errors[0].code).to_equal("E0712")
expect(errors[0].kind).to_equal(VhdlConstraintErrorKind.ClockDomainNameCollision)
expect(errors[0].message).to_contain("bus-domain")
expect(errors[0].message).to_contain("bus.domain")
expect(errors[0].message).to_contain("bus_domain")
```

</details>

#### reports incomplete sensitivity and latch coverage

1. span: test span
2. branch coverage: [
3. span: test span
   - Expected: errors.len() equals `2`
   - Expected: errors[0].code equals `E0720`
   - Expected: errors[0].kind equals `VhdlConstraintErrorKind.IncompleteSensitivity`
   - Expected: errors[1].code equals `E0722`
   - Expected: errors[1].kind equals `VhdlConstraintErrorKind.LatchInferred`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val checker = VhdlConstraintChecker.create()
checker.add_constraint(VhdlConstraint.SensitivityComplete(
    process_label: "p0",
    used_signals: ["clk", "rst", "data"],
    sensitivity: ["clk", "rst"],
    span: test_span()
))
checker.add_constraint(VhdlConstraint.NoLatchInference(
    process_label: "p1",
    assigned_signals: ["q"],
    branch_coverage: [("then", true), ("else", false)],
    span: test_span()
))

val errors = checker.check_all().unwrap_err()

expect(errors.len()).to_equal(2)
expect(errors[0].code).to_equal("E0720")
expect(errors[0].kind).to_equal(VhdlConstraintErrorKind.IncompleteSensitivity)
expect(errors[1].code).to_equal("E0722")
expect(errors[1].kind).to_equal(VhdlConstraintErrorKind.LatchInferred)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/vhdl_constraints_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Vhdl Constraints

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
