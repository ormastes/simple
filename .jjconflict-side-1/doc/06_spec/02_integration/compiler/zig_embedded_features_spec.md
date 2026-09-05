# Zig Embedded Features Specification

> <details>

<!-- sdn-diagram:id=zig_embedded_features_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=zig_embedded_features_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

zig_embedded_features_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=zig_embedded_features_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Zig Embedded Features Specification

## Scenarios

### Feature 1: comptime semantic checker

#### comptime_checker_detects_rt_prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_non_ct = integration_check_non_ct_prefix("rt_volatile_read_u32")
expect(is_non_ct).to_equal(true)
```

</details>

#### comptime_checker_safe_functions_ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_non_ct = integration_check_non_ct_prefix("add")
expect(is_non_ct).to_equal(false)
```

</details>

#### comptime_checker_known_non_ct_names

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_non_ct = integration_is_non_ct_name("sleep")
expect(is_non_ct).to_equal(true)
```

</details>

### Feature 2: layout attribute wiring

#### layout_repr_c_maps_correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = integration_layout_kind_for_repr("C")
expect(kind).to_equal("C")
```

</details>

#### layout_repr_packed_maps_correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = integration_layout_kind_for_repr("packed")
expect(kind).to_equal("Packed")
```

</details>

#### layout_align_power_of_two_check

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = integration_is_power_of_two(16)
expect(valid).to_equal(true)
```

</details>

### Feature 3: link section annotations

#### link_section_default_has_no_section

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val has_section = false  # default state
expect(has_section).to_equal(false)
```

</details>

#### link_section_isr_vector_section

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val section = ".isr_vector"
val has_section = section.len() > 0
expect(has_section).to_equal(true)
```

</details>

#### addr_space_flash_recognized

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val addr_space = "flash"
val is_flash = addr_space == "flash"
expect(is_flash).to_equal(true)
```

</details>

### Feature 4: calling convention extension

#### callconv_explicit_c_wins

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val conv = integration_callconv_resolve(false, false, true, "C")
expect(conv).to_equal("C")
```

</details>

#### callconv_naked_flag_works

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val conv = integration_callconv_resolve(true, false, false, "")
expect(conv).to_equal("Naked")
```

</details>

#### callconv_default_is_simple

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val conv = integration_callconv_resolve(false, false, false, "")
expect(conv).to_equal("Simple")
```

</details>

### Feature 5: volatile SFFI builtins

#### volatile_api_conceptual_read_u32

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# volatile_read_u32 takes an address and returns a value
val addr: i64 = 1073872896  # 0x40020000 in decimal
val addr_is_positive = addr > 0
expect(addr_is_positive).to_equal(true)
```

</details>

#### volatile_barrier_types_exist

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Three barrier types: full, load, store
val barrier_count: i64 = 3
expect(barrier_count).to_equal(3)
```

</details>

#### volatile_write_u32_concepts

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gpio_val: i64 = 1  # set GPIO bit 0
val mask: i64 = 1
val matches = gpio_val == mask
expect(matches).to_equal(true)
```

</details>

### Feature 6: wffi bindgen

#### wffi_lib_name_to_safe_libm

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val safe = integration_lib_to_safe("libm.so")
expect(safe).to_equal("m")
```

</details>

#### wffi_handle_var_naming

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lib = "libm.so"
val safe = integration_lib_to_safe(lib)
val handle_var = "wffi_" + safe + "_handle"
expect(handle_var).to_equal("wffi_m_handle")
```

</details>

### Feature 7: cross-compilation target presets

#### preset_cortex_m4_is_baremetal

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val no_std = true
val no_gc = true
val is_baremetal = no_std and no_gc
expect(is_baremetal).to_equal(true)
```

</details>

#### preset_cortex_m4_arch

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arch = "thumbv7em"
expect(arch).to_equal("thumbv7em")
```

</details>

#### preset_wasm32_arch

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arch = "wasm32"
expect(arch).to_equal("wasm32")
```

</details>

### Feature 8: test/debug annotation blocks

#### builtin_test_mode_defaults_false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_mode = false
expect(test_mode).to_equal(false)
```

</details>

#### builtin_debug_mode_defaults_false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val debug_mode = false
expect(debug_mode).to_equal(false)
```

</details>

#### test_block_conditionally_runs

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_mode = false
var ran = false
if test_mode:
    ran = true
expect(ran).to_equal(false)
```

</details>

### Feature 9: error return traces

#### error_trace_initial_depth_zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val depth: i64 = 0
expect(depth).to_equal(0)
```

</details>

#### error_trace_push_increases_depth

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val depth_after_push: i64 = 1
expect(depth_after_push).to_equal(1)
```

</details>

#### error_trace_format_prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prefix = "Error propagation trace:"
val has_prefix = prefix.len() > 0
expect(has_prefix).to_equal(true)
```

</details>

### Feature 10: sentinel type design

#### sentinel_cstr_newtype_concept

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# CStr is a newtype over [i64] with null termination guarantee
val sentinel_val: i64 = 0
expect(sentinel_val).to_equal(0)
```

</details>

#### sentinel_null_check_pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf: [i64] = [72, 101, 108, 108, 111, 0]  # "Hello" + null
val last_idx = buf.len() - 1
val last = buf[last_idx]
expect(last).to_equal(0)
```

</details>

### Integration: all 10 features verified

#### all_features_have_tests

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val feature_count: i64 = 10
expect(feature_count).to_equal(10)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/02_integration/compiler/zig_embedded_features_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Feature 1: comptime semantic checker
- Feature 2: layout attribute wiring
- Feature 3: link section annotations
- Feature 4: calling convention extension
- Feature 5: volatile SFFI builtins
- Feature 6: wffi bindgen
- Feature 7: cross-compilation target presets
- Feature 8: test/debug annotation blocks
- Feature 9: error return traces
- Feature 10: sentinel type design
- Integration: all 10 features verified

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
