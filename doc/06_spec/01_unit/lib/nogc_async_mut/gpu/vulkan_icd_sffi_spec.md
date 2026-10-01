# Vulkan Icd Sffi Specification

> Tests covering Vulkan ICD SFFI shim.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vulkan Icd Sffi Specification

## Scenarios

### Vulkan ICD SFFI shim

#### create_instance returns is_ok=true with positive handles

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- create_instance returns is_ok=true with positive handles
   - Expected: result.is_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("create_instance returns is_ok=true with positive handles")
val result = vk_icd_create_instance()
expect(result.is_ok).to_equal(true)
expect(result.instance_handle).to_be_greater_than(0)
expect(result.device_handle).to_be_greater_than(0)
expect(result.dispatch_handle).to_be_greater_than(0)
```

</details>

#### create_instance leaf field is dlopen or structured

- create_instance leaf field is dlopen or structured
   - Expected: leaf_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("create_instance leaf field is dlopen or structured")
val result = vk_icd_create_instance()
val leaf_ok = result.leaf == "dlopen" or result.leaf == "structured"
expect(leaf_ok).to_equal(true)
```

</details>

#### create_device on valid instance returns is_ok=true

- create_device on valid instance returns is_ok=true
   - Expected: dev.is_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("create_device on valid instance returns is_ok=true")
val inst = vk_icd_create_instance()
val dev = vk_icd_create_device(inst.instance_handle)
expect(dev.is_ok).to_equal(true)
expect(dev.device_handle).to_be_greater_than(0)
```

</details>

#### create_device carries leaf evidence

- create_device carries leaf evidence
   - Expected: leaf_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("create_device carries leaf evidence")
val inst = vk_icd_create_instance()
val dev = vk_icd_create_device(inst.instance_handle)
val leaf_ok = dev.leaf == "dlopen" or dev.leaf == "structured"
expect(leaf_ok).to_equal(true)
```

</details>

#### create_device on invalid instance returns error

- create_device on invalid instance returns error
   - Expected: result.is_ok is false
   - Expected: result.error equals `invalid-instance`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("create_device on invalid instance returns error")
val result = vk_icd_create_device(0)
expect(result.is_ok).to_equal(false)
expect(result.error).to_equal("invalid-instance")
```

</details>

#### destroy_instance does not panic on valid result

- destroy_instance does not panic on valid result
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("destroy_instance does not panic on valid result")
val result = vk_icd_create_instance()
vk_icd_destroy_instance(result)
expect(1).to_equal(1)
```

</details>

#### two create_instance calls return distinct instance handles

- two create_instance calls return distinct instance handles


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("two create_instance calls return distinct instance handles")
val r1 = vk_icd_create_instance()
val r2 = vk_icd_create_instance()
expect(r1.instance_handle).to_not_equal(r2.instance_handle)
```

</details>

#### vk_icd_probe_leaf returns leaf=dlopen or leaf=structured

- vk_icd_probe_leaf returns leaf=dlopen or leaf=structured
   - Expected: leaf_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("vk_icd_probe_leaf returns leaf=dlopen or leaf=structured")
val leaf = vk_icd_probe_leaf()
val leaf_ok = leaf == "leaf=dlopen" or leaf == "leaf=structured"
expect(leaf_ok).to_equal(true)
```

</details>

#### vk_icd_probe_leaf result starts with leaf=

- vk_icd_probe_leaf result starts with leaf=
   - Expected: starts_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("vk_icd_probe_leaf result starts with leaf=")
val leaf = vk_icd_probe_leaf()
val starts_ok = leaf.starts_with("leaf=")
expect(starts_ok).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/gpu/vulkan_icd_sffi_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Vulkan ICD SFFI shim.
- Vulkan ICD SFFI shim

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c1f1f381ebbc35b8f0c839c3b4fd1766cb62c723618d93661310b3a9eb60158b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c1f1f381ebbc35b8f0c839c3b4fd1766cb62c723618d93661310b3a9eb60158b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c1f1f381ebbc35b8f0c839c3b4fd1766cb62c723618d93661310b3a9eb60158b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/nogc_async_mut/gpu/vulkan_icd_sffi_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/gpu/vulkan_icd_sffi_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/gpu/vulkan_icd_sffi_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/gpu/vulkan_icd_sffi_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/gpu/vulkan_icd_sffi_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_async_mut/gpu/vulkan_icd_sffi_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'create_instance returns is_ok=true with positive handles' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/gpu/vulkan_icd_sffi_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'create_instance leaf field is dlopen or structured' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/gpu/vulkan_icd_sffi_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'create_device on valid instance returns is_ok=true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
