# Synthetic Driver Registration Specification

> <details>

<!-- sdn-diagram:id=synthetic_driver_registration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=synthetic_driver_registration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

synthetic_driver_registration_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=synthetic_driver_registration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Synthetic Driver Registration Specification

## Scenarios

### synthetic driver registration planner

#### recognizes an existing handwritten register_static_driver call with typed DriverOps

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (symbols, reg) = make_symbols_with_register()
val fn_ = make_function("register_null_block_driver", return_empty_call_block(reg), true, driver_attr())

val plan = plan_synthetic_driver_registration(fn_, symbols)

expect(plan.status).to_equal(SyntheticDriverRegistrationStatus.BlockedMissingDriverOps)
expect(plan.reason).to_contain("DriverOps argument is not identifiable")
expect(plan.has_ops_value).to_equal(false)
```

</details>

#### is ready to synthesize when @driver has a typed DriverOps value in scope

1. var symbols = SymbolTable new
2. define driver ops value
   - Expected: plan.status equals `SyntheticDriverRegistrationStatus.ReadyToSynthesize`
   - Expected: plan.has_ops_value is true
   - Expected: plan.ops_value_name equals `null_block_ops`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = SymbolTable.new()
val fn_ = make_function("register_null_block_driver", plain_block(), true, driver_attr())

val plan = plan_synthetic_driver_registration(fn_, symbols)

expect(plan.status).to_equal(SyntheticDriverRegistrationStatus.BlockedMissingDriverOps)
expect(plan.reason).to_contain("DriverOps value")
```

</details>

#### blocks @native_lib synthesis when adapter functions are absent

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = SymbolTable.new()
val fn_ = make_function("register_cuda_ffi_native_lib", plain_block(), true, native_attr())

val plan = plan_synthetic_driver_registration(fn_, symbols)

expect(plan.status).to_equal(SyntheticDriverRegistrationStatus.BlockedNativeLibOps)
expect(plan.reason).to_contain("adapter functions")
```

</details>

#### ignores functions without driver manifest metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
