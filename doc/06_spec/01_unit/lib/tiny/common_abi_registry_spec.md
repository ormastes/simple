# Common Abi Registry Specification

> Tests covering tiny ABI descriptors and static registry.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Common Abi Registry Specification

## Scenarios

### tiny ABI descriptors and static registry

#### keeps runtime component IDs aligned with the manifest range

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### accepts complete module metadata and bounded dependency spans

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(tiny_module_validate(gui_module([pane_descriptor()]), 2, 2).code).to_equal(TINY_OK)
```

</details>

#### rejects invalid dependency spans and duplicate class IDs

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pane = pane_descriptor()
val bad_span = TinyClassDescriptorV1(class_id: 4098, stable_name_hash: 4098, name_offset: 4, name_length: 4, capability_bits: 1, dependency_first: 1, dependency_count: 1, factory_entry_id: 103, destroy_entry_id: 104)
expect(tiny_module_validate(gui_module([bad_span]), 2, 2).code).to_equal(TINY_ERR_MALFORMED)
expect(tiny_module_validate(gui_module([pane, pane]), 2, 2).code).to_equal(TINY_ERR_MALFORMED)
```

</details>

#### validates the versioned draw stream envelope

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stream = TinyDrawStreamV1(abi_major: TINY_ABI_MAJOR, abi_minor: TINY_ABI_MINOR, format_id: TINY_DRAW_STREAM_FORMAT_V1, stable_name_hash: 9001, name_offset: 0, name_length: 8, words: [0], word_count: 1)
expect(tiny_draw_stream_validate(stream, 4, 8).code).to_equal(TINY_OK)
val oversized = TinyDrawStreamV1(abi_major: TINY_ABI_MAJOR, abi_minor: TINY_ABI_MINOR, format_id: TINY_DRAW_STREAM_FORMAT_V1, stable_name_hash: 9001, name_offset: 0, name_length: 8, words: [0], word_count: 2)
expect(tiny_draw_stream_validate(oversized, 4, 8).code).to_equal(TINY_ERR_CAPACITY)
```

</details>

#### registers and queries modules and classes without symbol lookup

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var registry = TinyStaticRegistryV1.bounded(2, 2, 2)
expect(registry.register(gui_module([pane_descriptor()])).code).to_equal(TINY_OK)
expect(registry.require_module(1).code).to_equal(TINY_OK)
expect(registry.require_class(TINY_COMPONENT_PANE).code).to_equal(TINY_OK)
expect(registry.require_class(9999).code).to_equal(TINY_ERR_INVALID)
expect(registry.register(gui_module([pane_descriptor()])).code).to_equal(TINY_ERR_INVALID)
```

</details>

#### rejects class IDs already owned by another registered module

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var registry = TinyStaticRegistryV1.bounded(3, 2, 2)
expect(registry.register(module_with_id(1, [pane_descriptor()])).code).to_equal(TINY_OK)
expect(registry.register(module_with_id(2, [pane_descriptor()])).code).to_equal(TINY_ERR_INVALID)
expect(registry.modules.len()).to_equal(1)
expect(registry.modules[0].classes[0].factory_entry_id).to_equal(101)
```

</details>

#### rejects an incompatible ABI before mutating registry state

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var registry = TinyStaticRegistryV1.bounded(2, 2, 2)
val valid = module_with_id(1, [pane_descriptor()])
val incompatible = TinyModuleV1(abi_major: TINY_ABI_MAJOR + 1, abi_minor: valid.abi_minor, module_id: valid.module_id, stable_name_hash: valid.stable_name_hash, name_offset: valid.name_offset, name_length: valid.name_length, name_bytes_length: valid.name_bytes_length, capability_bits: valid.capability_bits, init_entry_id: valid.init_entry_id, shutdown_entry_id: valid.shutdown_entry_id, query_entry_id: valid.query_entry_id, classes: valid.classes, dependencies: valid.dependencies)
expect(registry.register(incompatible).code).to_equal(TINY_ERR_ABI)
expect(registry.modules.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/tiny/common_abi_registry_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering tiny ABI descriptors and static registry.
- tiny ABI descriptors and static registry

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `2a2967d8f4d4278811d8a7fef9ea4e53d99f168bea4fb041feefe984fb4f8eec`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2a2967d8f4d4278811d8a7fef9ea4e53d99f168bea4fb041feefe984fb4f8eec`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2a2967d8f4d4278811d8a7fef9ea4e53d99f168bea4fb041feefe984fb4f8eec`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **83/100**; blockers: **0**.

SSpec documentization score: 83/100
source: test/01_unit/lib/tiny/common_abi_registry_spec.spl
mirror: doc/06_spec/01_unit/lib/tiny/common_abi_registry_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=60 oracle=70
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/tiny/common_abi_registry_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/tiny/common_abi_registry_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/tiny/common_abi_registry_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/lib/tiny/common_abi_registry_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/tiny/common_abi_registry_spec.spl:25:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'keeps runtime component IDs aligned with the manifest range' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/tiny/common_abi_registry_spec.spl:31:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'accepts complete module metadata and bounded dependency spans' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/tiny/common_abi_registry_spec.spl:34:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'rejects invalid dependency spans and duplicate class IDs' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/tiny/common_abi_registry_spec.spl:40:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'validates the versioned draw stream envelope' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
