# Synthetic Driver Registration Specification

> Tests covering synthetic driver registration planner.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Synthetic Driver Registration Specification

## Scenarios

### synthetic driver registration planner

#### recognizes an existing handwritten register_static_driver call with typed DriverOps

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- recognizes an existing handwritten register_static_driver call with typed DriverOps
   - Expected: plan.status equals `SyntheticDriverRegistrationStatus.AlreadyHandwritten`
   - Expected: plan.has_ops_value is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes an existing handwritten register_static_driver call with typed DriverOps")
val (symbols, reg) = make_symbols_with_register()
val manifest = define_manifest_value(symbols)
val ops = define_driver_ops_value(symbols, "ops")
val fn_ = make_function("register_null_block_driver", return_call_block(reg, manifest, ops), true, driver_attr())

val plan = plan_synthetic_driver_registration(fn_, symbols)

expect(plan.status).to_equal(SyntheticDriverRegistrationStatus.AlreadyHandwritten)
expect(plan.reason).to_contain("already calls register_static_driver")
expect(plan.has_ops_value).to_equal(true)
```

</details>

#### does not treat a register_static_driver call without DriverOps as complete

- does not treat a register_static_driver call without DriverOps as complete
   - Expected: plan.status equals `SyntheticDriverRegistrationStatus.BlockedMissingDriverOps`
   - Expected: plan.has_ops_value is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not treat a register_static_driver call without DriverOps as complete")
val (symbols, reg) = make_symbols_with_register()
val fn_ = make_function("register_null_block_driver", return_empty_call_block(reg), true, driver_attr())

val plan = plan_synthetic_driver_registration(fn_, symbols)

expect(plan.status).to_equal(SyntheticDriverRegistrationStatus.BlockedMissingDriverOps)
expect(plan.reason).to_contain("DriverOps argument is not identifiable")
expect(plan.has_ops_value).to_equal(false)
```

</details>

#### is ready to synthesize when @driver has a typed DriverOps value in scope

- is ready to synthesize when @driver has a typed DriverOps value in scope
   - Expected: plan.status equals `SyntheticDriverRegistrationStatus.ReadyToSynthesize`
   - Expected: plan.has_ops_value is true
   - Expected: plan.ops_value_name equals `null_block_ops`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is ready to synthesize when @driver has a typed DriverOps value in scope")
var symbols = SymbolTable.new()
define_driver_ops_value(symbols, "null_block_ops")
val fn_ = make_function("register_null_block_driver", plain_block(), true, driver_attr())

val plan = plan_synthetic_driver_registration(fn_, symbols)

expect(plan.status).to_equal(SyntheticDriverRegistrationStatus.ReadyToSynthesize)
expect(plan.has_ops_value).to_equal(true)
expect(plan.ops_value_name).to_equal("null_block_ops")
```

</details>

#### blocks @driver synthesis when DriverOps source is absent

- blocks @driver synthesis when DriverOps source is absent
   - Expected: plan.status equals `SyntheticDriverRegistrationStatus.BlockedMissingDriverOps`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocks @driver synthesis when DriverOps source is absent")
val symbols = SymbolTable.new()
val fn_ = make_function("register_null_block_driver", plain_block(), true, driver_attr())

val plan = plan_synthetic_driver_registration(fn_, symbols)

expect(plan.status).to_equal(SyntheticDriverRegistrationStatus.BlockedMissingDriverOps)
expect(plan.reason).to_contain("DriverOps value")
```

</details>

#### blocks @native_lib synthesis when adapter functions are absent

- blocks @native_lib synthesis when adapter functions are absent
   - Expected: plan.status equals `SyntheticDriverRegistrationStatus.BlockedNativeLibOps`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocks @native_lib synthesis when adapter functions are absent")
val symbols = SymbolTable.new()
val fn_ = make_function("register_cuda_ffi_native_lib", plain_block(), true, native_attr())

val plan = plan_synthetic_driver_registration(fn_, symbols)

expect(plan.status).to_equal(SyntheticDriverRegistrationStatus.BlockedNativeLibOps)
expect(plan.reason).to_contain("adapter functions")
```

</details>

#### ignores functions without driver manifest metadata

- ignores functions without driver manifest metadata
   - Expected: plan.status equals `SyntheticDriverRegistrationStatus.NoManifest`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ignores functions without driver manifest metadata")
val symbols = SymbolTable.new()
val fn_ = make_function("helper", plain_block(), false, driver_attr())

val plan = plan_synthetic_driver_registration(fn_, symbols)

expect(plan.status).to_equal(SyntheticDriverRegistrationStatus.NoManifest)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/synthetic_driver_registration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering synthetic driver registration planner.
- synthetic driver registration planner

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `09b7247e6a0e156560e844b2fa2bff8a4a18e418117fabf96c16ac937afc2770`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `09b7247e6a0e156560e844b2fa2bff8a4a18e418117fabf96c16ac937afc2770`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `09b7247e6a0e156560e844b2fa2bff8a4a18e418117fabf96c16ac937afc2770`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/mir/synthetic_driver_registration_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir/synthetic_driver_registration_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mir/synthetic_driver_registration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir/synthetic_driver_registration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir/synthetic_driver_registration_spec.spl:173:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recognizes an existing handwritten register_static_driver call with typed DriverOps' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/synthetic_driver_registration_spec.spl:187:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not treat a register_static_driver call without DriverOps as complete' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/synthetic_driver_registration_spec.spl:199:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is ready to synthesize when @driver has a typed DriverOps value in scope' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
