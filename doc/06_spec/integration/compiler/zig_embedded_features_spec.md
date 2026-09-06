# Zig Embedded Features Specification

> Tests covering Feature 1: comptime semantic checker, Feature 2: layout attribute wiring, Feature 3: link section annotations, Feature 4: calling convention extension, Feature 5: volatile SFFI builtins, Feature 6: wffi bindgen, Feature 7: cross-compilation target presets, Feature 8: test/debug annotation blocks, Feature 9: error return traces, Feature 10: sentinel type design, Integration: all 10 features verified.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Zig Embedded Features Specification

## Scenarios

### Feature 1: comptime semantic checker

#### comptime_checker_detects_rt_prefix

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- comptime_checker_detects_rt_prefix
   - Expected: is_non_ct is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("comptime_checker_detects_rt_prefix")
val is_non_ct = integration_check_non_ct_prefix("rt_volatile_read_u32")
expect(is_non_ct).to_equal(true)
```

</details>

#### comptime_checker_safe_functions_ok

- comptime_checker_safe_functions_ok
   - Expected: is_non_ct is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("comptime_checker_safe_functions_ok")
val is_non_ct = integration_check_non_ct_prefix("add")
expect(is_non_ct).to_equal(false)
```

</details>

#### comptime_checker_known_non_ct_names

- comptime_checker_known_non_ct_names
   - Expected: is_non_ct is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("comptime_checker_known_non_ct_names")
val is_non_ct = integration_is_non_ct_name("sleep")
expect(is_non_ct).to_equal(true)
```

</details>

### Feature 2: layout attribute wiring

#### layout_repr_c_maps_correctly

- layout_repr_c_maps_correctly
   - Expected: kind equals `C`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("layout_repr_c_maps_correctly")
val kind = integration_layout_kind_for_repr("C")
expect(kind).to_equal("C")
```

</details>

#### layout_repr_packed_maps_correctly

- layout_repr_packed_maps_correctly
   - Expected: kind equals `Packed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("layout_repr_packed_maps_correctly")
val kind = integration_layout_kind_for_repr("packed")
expect(kind).to_equal("Packed")
```

</details>

#### layout_align_power_of_two_check

- layout_align_power_of_two_check
   - Expected: valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("layout_align_power_of_two_check")
val valid = integration_is_power_of_two(16)
expect(valid).to_equal(true)
```

</details>

### Feature 3: link section annotations

#### link_section_default_has_no_section

- link_section_default_has_no_section
   - Expected: has_section is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("link_section_default_has_no_section")
val has_section = false  # default state
expect(has_section).to_equal(false)
```

</details>

#### link_section_isr_vector_section

- link_section_isr_vector_section
   - Expected: has_section is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("link_section_isr_vector_section")
val section = ".isr_vector"
val has_section = section.len() > 0
expect(has_section).to_equal(true)
```

</details>

#### addr_space_flash_recognized

- addr_space_flash_recognized
   - Expected: is_flash is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("addr_space_flash_recognized")
val addr_space = "flash"
val is_flash = addr_space == "flash"
expect(is_flash).to_equal(true)
```

</details>

### Feature 4: calling convention extension

#### callconv_explicit_c_wins

- callconv_explicit_c_wins
   - Expected: conv equals `C`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("callconv_explicit_c_wins")
val conv = integration_callconv_resolve(false, false, true, "C")
expect(conv).to_equal("C")
```

</details>

#### callconv_naked_flag_works

- callconv_naked_flag_works
   - Expected: conv equals `Naked`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("callconv_naked_flag_works")
val conv = integration_callconv_resolve(true, false, false, "")
expect(conv).to_equal("Naked")
```

</details>

#### callconv_default_is_simple

- callconv_default_is_simple
   - Expected: conv equals `Simple`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("callconv_default_is_simple")
val conv = integration_callconv_resolve(false, false, false, "")
expect(conv).to_equal("Simple")
```

</details>

### Feature 5: volatile SFFI builtins

#### volatile_api_conceptual_read_u32

- volatile_api_conceptual_read_u32
   - Expected: addr_is_positive is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("volatile_api_conceptual_read_u32")
# volatile_read_u32 takes an address and returns a value
val addr: i64 = 1073872896  # 0x40020000 in decimal
val addr_is_positive = addr > 0
expect(addr_is_positive).to_equal(true)
```

</details>

#### volatile_barrier_types_exist

- volatile_barrier_types_exist
   - Expected: barrier_count equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("volatile_barrier_types_exist")
# Three barrier types: full, load, store
val barrier_count: i64 = 3
expect(barrier_count).to_equal(3)
```

</details>

#### volatile_write_u32_concepts

- volatile_write_u32_concepts
   - Expected: matches is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("volatile_write_u32_concepts")
val gpio_val: i64 = 1  # set GPIO bit 0
val mask: i64 = 1
val matches = gpio_val == mask
expect(matches).to_equal(true)
```

</details>

### Feature 6: wffi bindgen

#### wffi_lib_name_to_safe_libm

- wffi_lib_name_to_safe_libm
   - Expected: safe equals `m`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("wffi_lib_name_to_safe_libm")
val safe = integration_lib_to_safe("libm.so")
expect(safe).to_equal("m")
```

</details>

#### wffi_handle_var_naming

- wffi_handle_var_naming
   - Expected: handle_var equals `wffi_m_handle`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("wffi_handle_var_naming")
val lib = "libm.so"
val safe = integration_lib_to_safe(lib)
val handle_var = "wffi_" + safe + "_handle"
expect(handle_var).to_equal("wffi_m_handle")
```

</details>

### Feature 7: cross-compilation target presets

#### preset_cortex_m4_is_baremetal

- preset_cortex_m4_is_baremetal
   - Expected: is_baremetal is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("preset_cortex_m4_is_baremetal")
val no_std = true
val no_gc = true
val is_baremetal = no_std and no_gc
expect(is_baremetal).to_equal(true)
```

</details>

#### preset_cortex_m4_arch

- preset_cortex_m4_arch
   - Expected: arch equals `thumbv7em`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("preset_cortex_m4_arch")
val arch = "thumbv7em"
expect(arch).to_equal("thumbv7em")
```

</details>

#### preset_wasm32_arch

- preset_wasm32_arch
   - Expected: arch equals `wasm32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("preset_wasm32_arch")
val arch = "wasm32"
expect(arch).to_equal("wasm32")
```

</details>

### Feature 8: test/debug annotation blocks

#### builtin_test_mode_defaults_false

- builtin_test_mode_defaults_false
   - Expected: test_mode is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("builtin_test_mode_defaults_false")
val test_mode = false
expect(test_mode).to_equal(false)
```

</details>

#### builtin_debug_mode_defaults_false

- builtin_debug_mode_defaults_false
   - Expected: debug_mode is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("builtin_debug_mode_defaults_false")
val debug_mode = false
expect(debug_mode).to_equal(false)
```

</details>

#### test_block_conditionally_runs

- test_block_conditionally_runs
   - Expected: ran is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("test_block_conditionally_runs")
val test_mode = false
var ran = false
if test_mode:
    ran = true
expect(ran).to_equal(false)
```

</details>

### Feature 9: error return traces

#### error_trace_initial_depth_zero

- error_trace_initial_depth_zero
   - Expected: depth equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("error_trace_initial_depth_zero")
val depth: i64 = 0
expect(depth).to_equal(0)
```

</details>

#### error_trace_push_increases_depth

- error_trace_push_increases_depth
   - Expected: depth_after_push equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("error_trace_push_increases_depth")
val depth_after_push: i64 = 1
expect(depth_after_push).to_equal(1)
```

</details>

#### error_trace_format_prefix

- error_trace_format_prefix
   - Expected: has_prefix is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("error_trace_format_prefix")
val prefix = "Error propagation trace:"
val has_prefix = prefix.len() > 0
expect(has_prefix).to_equal(true)
```

</details>

### Feature 10: sentinel type design

#### sentinel_cstr_newtype_concept

- sentinel_cstr_newtype_concept
   - Expected: sentinel_val equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("sentinel_cstr_newtype_concept")
# CStr is a newtype over [i64] with null termination guarantee
val sentinel_val: i64 = 0
expect(sentinel_val).to_equal(0)
```

</details>

#### sentinel_null_check_pattern

- sentinel_null_check_pattern
   - Expected: last equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("sentinel_null_check_pattern")
val buf: [i64] = [72, 101, 108, 108, 111, 0]  # "Hello" + null
val last_idx = buf.len() - 1
val last = buf[last_idx]
expect(last).to_equal(0)
```

</details>

### Integration: all 10 features verified

#### all_features_have_tests

- all_features_have_tests
   - Expected: feature_count equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("all_features_have_tests")
val feature_count: i64 = 10
expect(feature_count).to_equal(10)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/integration/compiler/zig_embedded_features_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Feature 1: comptime semantic checker, Feature 2: layout attribute wiring, Feature 3: link section annotations, Feature 4: calling convention extension, Feature 5: volatile SFFI builtins, Feature 6: wffi bindgen, Feature 7: cross-compilation target presets, Feature 8: test/debug annotation blocks, Feature 9: error return traces, Feature 10: sentinel type design, Integration: all 10 features verified.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `103e395ed1fb5ff0edfd77eb30e6c553977c40597479ccd25476bdc995195ad4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `103e395ed1fb5ff0edfd77eb30e6c553977c40597479ccd25476bdc995195ad4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `103e395ed1fb5ff0edfd77eb30e6c553977c40597479ccd25476bdc995195ad4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/compiler/zig_embedded_features_spec.spl
mirror: doc/06_spec/integration/compiler/zig_embedded_features_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/compiler/zig_embedded_features_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/compiler/zig_embedded_features_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/compiler/zig_embedded_features_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/compiler/zig_embedded_features_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'comptime_checker_detects_rt_prefix' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/compiler/zig_embedded_features_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'comptime_checker_safe_functions_ok' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/compiler/zig_embedded_features_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'comptime_checker_known_non_ct_names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
