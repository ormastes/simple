# common_abi_registry_spec

> Verifies the common abi registry behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# common_abi_registry_spec

Verifies the common abi registry behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/tiny/common_abi_registry_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the common abi registry behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### tiny ABI descriptors and static registry

#### keeps runtime component IDs aligned with the manifest range

- Verify: keeps runtime component IDs aligned with the manifest range
   - Expected: TINY_COMPONENT_PANE equals `4097)  # oracle: pinned constant asserted by this scenario`
   - Expected: TINY_COMPONENT_PROGRESS equals `4110)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TINY_COMMON_ABI_REGISTRY-001
step("Verify: keeps runtime component IDs aligned with the manifest range")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(TINY_COMPONENT_PANE).to_equal(4097)  # oracle: pinned constant asserted by this scenario
expect(TINY_COMPONENT_PROGRESS).to_equal(4110)  # oracle: pinned constant asserted by this scenario
```

</details>

#### accepts complete module metadata and bounded dependency spans

- Verify: accepts complete module metadata and bounded dependency spans
   - Expected: tiny_module_validate(gui_module([pane_descriptor()]), 2, 2).code equals `TINY_OK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TINY_COMMON_ABI_REGISTRY-001
step("Verify: accepts complete module metadata and bounded dependency spans")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(tiny_module_validate(gui_module([pane_descriptor()]), 2, 2).code).to_equal(TINY_OK)
```

</details>

#### rejects invalid dependency spans and duplicate class IDs

- Verify: rejects invalid dependency spans and duplicate class IDs
   - Expected: tiny_module_validate(gui_module([bad_span]), 2, 2).code equals `TINY_ERR_MALFORMED`
   - Expected: tiny_module_validate(gui_module([pane, pane]), 2, 2).code equals `TINY_ERR_MALFORMED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TINY_COMMON_ABI_REGISTRY-001
step("Verify: rejects invalid dependency spans and duplicate class IDs")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val pane = pane_descriptor()
val bad_span = TinyClassDescriptorV1(class_id: 4098, stable_name_hash: 4098, name_offset: 4, name_length: 4, capability_bits: 1, dependency_first: 1, dependency_count: 1, factory_entry_id: 103, destroy_entry_id: 104)
expect(tiny_module_validate(gui_module([bad_span]), 2, 2).code).to_equal(TINY_ERR_MALFORMED)
expect(tiny_module_validate(gui_module([pane, pane]), 2, 2).code).to_equal(TINY_ERR_MALFORMED)
```

</details>

#### validates the versioned draw stream envelope

- Verify: validates the versioned draw stream envelope
   - Expected: tiny_draw_stream_validate(stream, 4, 8).code equals `TINY_OK`
   - Expected: tiny_draw_stream_validate(oversized, 4, 8).code equals `TINY_ERR_CAPACITY`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TINY_COMMON_ABI_REGISTRY-001
step("Verify: validates the versioned draw stream envelope")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val stream = TinyDrawStreamV1(abi_major: TINY_ABI_MAJOR, abi_minor: TINY_ABI_MINOR, format_id: TINY_DRAW_STREAM_FORMAT_V1, stable_name_hash: 9001, name_offset: 0, name_length: 8, words: [0], word_count: 1)
expect(tiny_draw_stream_validate(stream, 4, 8).code).to_equal(TINY_OK)
val oversized = TinyDrawStreamV1(abi_major: TINY_ABI_MAJOR, abi_minor: TINY_ABI_MINOR, format_id: TINY_DRAW_STREAM_FORMAT_V1, stable_name_hash: 9001, name_offset: 0, name_length: 8, words: [0], word_count: 2)
expect(tiny_draw_stream_validate(oversized, 4, 8).code).to_equal(TINY_ERR_CAPACITY)
```

</details>

#### registers and queries modules and classes without symbol lookup

- Verify: registers and queries modules and classes without symbol lookup
   - Expected: registry.register(gui_module([pane_descriptor()])).code equals `TINY_OK`
   - Expected: registry.require_module(1).code equals `TINY_OK`
   - Expected: registry.require_class(TINY_COMPONENT_PANE).code equals `TINY_OK`
   - Expected: registry.require_class(9999).code equals `TINY_ERR_INVALID`
   - Expected: registry.register(gui_module([pane_descriptor()])).code equals `TINY_ERR_INVALID`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TINY_COMMON_ABI_REGISTRY-001
step("Verify: registers and queries modules and classes without symbol lookup")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var registry = TinyStaticRegistryV1.bounded(2, 2, 2)
expect(registry.register(gui_module([pane_descriptor()])).code).to_equal(TINY_OK)
expect(registry.require_module(1).code).to_equal(TINY_OK)
expect(registry.require_class(TINY_COMPONENT_PANE).code).to_equal(TINY_OK)
expect(registry.require_class(9999).code).to_equal(TINY_ERR_INVALID)
expect(registry.register(gui_module([pane_descriptor()])).code).to_equal(TINY_ERR_INVALID)
```

</details>

#### rejects class IDs already owned by another registered module

- Verify: rejects class IDs already owned by another registered module
   - Expected: registry.register(module_with_id(1, [pane_descriptor()])).code equals `TINY_OK`
   - Expected: registry.register(module_with_id(2, [pane_descriptor()])).code equals `TINY_ERR_INVALID`
   - Expected: registry.modules.len() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: registry.modules[0].classes[0].factory_entry_id equals `101)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TINY_COMMON_ABI_REGISTRY-001
step("Verify: rejects class IDs already owned by another registered module")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var registry = TinyStaticRegistryV1.bounded(3, 2, 2)
expect(registry.register(module_with_id(1, [pane_descriptor()])).code).to_equal(TINY_OK)
expect(registry.register(module_with_id(2, [pane_descriptor()])).code).to_equal(TINY_ERR_INVALID)
expect(registry.modules.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(registry.modules[0].classes[0].factory_entry_id).to_equal(101)  # oracle: pinned constant asserted by this scenario
```

</details>

#### rejects an incompatible ABI before mutating registry state

- Verify: rejects an incompatible ABI before mutating registry state
   - Expected: registry.register(incompatible).code equals `TINY_ERR_ABI`
   - Expected: registry.modules.len() equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TINY_COMMON_ABI_REGISTRY-001
step("Verify: rejects an incompatible ABI before mutating registry state")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var registry = TinyStaticRegistryV1.bounded(2, 2, 2)
val valid = module_with_id(1, [pane_descriptor()])
val incompatible = TinyModuleV1(abi_major: TINY_ABI_MAJOR + 1, abi_minor: valid.abi_minor, module_id: valid.module_id, stable_name_hash: valid.stable_name_hash, name_offset: valid.name_offset, name_length: valid.name_length, name_bytes_length: valid.name_bytes_length, capability_bits: valid.capability_bits, init_entry_id: valid.init_entry_id, shutdown_entry_id: valid.shutdown_entry_id, query_entry_id: valid.query_entry_id, classes: valid.classes, dependencies: valid.dependencies)
expect(registry.register(incompatible).code).to_equal(TINY_ERR_ABI)
expect(registry.modules.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7241e6a1011338fa3594057a29ae14bc8ee7b808b414be30681241f647743521`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7241e6a1011338fa3594057a29ae14bc8ee7b808b414be30681241f647743521`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7241e6a1011338fa3594057a29ae14bc8ee7b808b414be30681241f647743521`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/lib/tiny/common_abi_registry_spec.spl
mirror: doc/06_spec/01_unit/lib/tiny/common_abi_registry_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/tiny/common_abi_registry_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/lib/tiny/common_abi_registry_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/tiny/common_abi_registry_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
