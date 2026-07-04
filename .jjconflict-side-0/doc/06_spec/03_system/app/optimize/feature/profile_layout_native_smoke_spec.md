# Profile Layout Native Smoke Specification

> <details>

<!-- sdn-diagram:id=profile_layout_native_smoke_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=profile_layout_native_smoke_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

profile_layout_native_smoke_spec -> std
profile_layout_native_smoke_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=profile_layout_native_smoke_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Profile Layout Native Smoke Specification

## Scenarios

### Profile Layout Native Smoke

#### should expose a fixture with matching source manifest and sprof symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(profile_layout_native_smoke_source_text()).to_contain("fn dispatch")
expect(profile_layout_native_smoke_manifest_text()).to_contain("symbol=dispatch")
expect(profile_layout_native_smoke_profile_text()).to_contain("function;key=c:dispatch:entry")
```

</details>

#### should compile baseline and section-mapped native binaries and report measured evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = profile_layout_native_smoke_run("/tmp/simple_profile_layout_native_smoke_spec_" + rt_getpid().to_string(), 2)

expect(evidence.status == "ok" or evidence.status == "regression").to_equal(true)
expect(evidence.applied_count).to_equal(3)
expect(evidence.baseline_ms).to_be_greater_than(0)
expect(evidence.optimized_ms).to_be_greater_than(0)
expect(evidence.baseline_size_bytes).to_be_greater_than(0)
expect(evidence.optimized_size_bytes).to_be_greater_than(0)
expect(evidence.mapped_c_source).to_contain("SIMPLE_LAYOUT_SECTION_dispatch static int dispatch(void) {")
expect(evidence.optimized_symbol_order_verified).to_equal(true)
expect(evidence.optimized_symbol_order_text).to_contain("_ZL8dispatchv")
expect(evidence.optimized_symbol_order_text).to_contain("_ZL5parsev")
expect(evidence.optimized_symbol_order_text).to_contain("_ZL4rarev")
expect(evidence.non_profile_counter_symbol_count).to_equal(0)
```

</details>

#### should run representative counters through sprof layout native rebuild and measurement

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = profile_layout_representative_full_flow_run("/tmp/simple_profile_layout_representative_spec_" + rt_getpid().to_string(), 2)

expect(profile_layout_representative_c_source_text()).to_contain("for (int i = 0; i < 200; ++i)")
expect(evidence.status == "ok" or evidence.status == "regression").to_equal(true)
expect(evidence.profile_exit_code).to_equal(0)
expect(evidence.snapshot_status).to_equal("valid")
expect(evidence.sprof_wrote).to_equal(true)
expect(evidence.sprof_record_count).to_be_greater_than(3)
expect(evidence.loaded_profile_status).to_equal("loaded")
expect(evidence.loaded_function_merged_count).to_be_greater_than(200)
expect(evidence.applied_count).to_equal(3)
expect(evidence.optimized_symbol_order_verified).to_equal(true)
expect(evidence.non_profile_counter_symbol_count).to_equal(0)
expect(evidence.baseline_ms).to_be_greater_than(0)
expect(evidence.optimized_ms).to_be_greater_than(0)
expect(evidence.baseline_size_bytes).to_be_greater_than(0)
expect(evidence.optimized_size_bytes).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/optimize/feature/profile_layout_native_smoke_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Profile Layout Native Smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
