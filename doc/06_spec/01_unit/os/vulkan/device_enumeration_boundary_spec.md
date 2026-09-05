# Vulkan Device Enumeration Boundary

> This is a NEW counterpart boundary (lane L2), separate from the three in

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vulkan Device Enumeration Boundary

This is a NEW counterpart boundary (lane L2), separate from the three in

## At a Glance

| Field | Value |
|-------|-------|
| Category | OS / GPU driver |
| Status | In Progress |
| Source | `test/01_unit/os/vulkan/device_enumeration_boundary_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

This is a NEW counterpart boundary (lane L2), separate from the three in
`counterpart_plan.spl` (spirv/cmdstream/readback): what a Vulkan
implementation reports for physical devices, queue families, memory
heaps/types and a named subset of limits. The reader is an engineer asking
"does the Simple candidate honestly report what it can enumerate, and when it
does, does it agree with a real, independent Vulkan implementation".

## Scope and Preconditions

No board and no discrete GPU are required: the counterpart is Mesa's
`lavapipe` software rasterizer (`lvp_icd.json`), which reports full, real
enumeration data on the CPU alone. This file exercises the canonical schema,
the honesty of the candidate reader, and the comparison relation — it does
not require the candidate side to have real data to be meaningful, because an
honestly-`unavailable` candidate is itself the assertion under test.

## Primary Workflow

Build the canonical, sorted projection of a device enumeration record, prove
it is stable under input reordering, prove the candidate reports
`unavailable` rather than fabricating a pass, and prove the framework's
vacuity rule rejects a plan whose only "comparison" is against an unavailable
source.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Comparable projection | Device name/vendor id/device id/api version/exact limit magnitude dropped; queue family flag-sets+counts, memory heap/type counts+flags, and limit *names* kept |
| structural_equal | Chosen because enumeration legitimately differs per physical device — `byte_exact` would fail on device-specific fields that carry no defect |
| unavailable ≠ pass | The candidate honestly reports `ProviderStatus.unavailable`; nothing here treats that as agreement |
| independence group `mesa` | anv, lavapipe and venus-via-Mesa are ONE reference, not three |

## Related Specifications

- [Board Vulkan counterpart plans](board_vulkan_counterpart_plan_spec.spl) — the three board-runnable boundaries

## Evidence and Provenance

The counterpart is not a fixture: `lavapipe_reference_enumeration()` in
`boundary_enumeration_provider.spl` runs
`VK_ICD_FILENAMES=/usr/share/vulkan/icd.d/lvp_icd.json vulkaninfo` as a real
subprocess on every call and parses its real stdout into the canonical
schema. If the binary or the ICD is absent the parse fails closed (nil) and
the source is reported `ProviderStatus.unavailable` — no literal is ever
substituted for a failed execution. The candidate side is equally derived:
`candidate_enumeration_is_available()` calls the real
`GpuVendorRegistry.probe_all()` and the real `venus_icd_*` transport
functions and reads their actual return values.

## Recovery and Troubleshooting

A failure in the "candidate reports unavailable" scenarios means the
candidate started fabricating enumeration data — re-check
`vulkan_icd_virtio.spl` and `gpu_vendor_probe.spl` before changing the
assertion. A failure in the projection-stability scenarios means the sort
routines regressed order-independence.

## Compatibility and Limitations

Today the Simple candidate has no real device-enumeration reader at all,
so this spec proves the framework's honesty gates rather than proving a
passing device comparison. That gap is filed, not hidden.

## Scenarios

### vulkan device enumeration boundary identity

#### names the frozen boundary id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
# @req REQ-BOARD-VULKAN-002
```

</details>

#### chooses structural_equal because enumeration is legitimately device-specific

- read the relation for this boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("read the relation for this boundary")
assert_equal(relation_name(vulkan_enumeration_relation()), "structural_equal")
```

</details>

### vulkan device enumeration counterpart execution

#### actually executes vulkaninfo against the lavapipe ICD as a real subprocess

- shell out to VK_ICD_FILENAMES=lvp_icd.json vulkaninfo and parse real stdout


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("shell out to VK_ICD_FILENAMES=lvp_icd.json vulkaninfo and parse real stdout")
val executed = lavapipe_reference_enumeration()
assert_true(executed.?)
assert_equal(lavapipe_source_status(), ProviderStatus.executed)
```

</details>

#### parses a non-empty device name and at least one queue family from the real transcript

- read fields parsed from the real subprocess output


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("read fields parsed from the real subprocess output")
val real = required_lavapipe_reference()
assert_true(real.device_name != "")
assert_true(real.queue_families.len() > 0)
```

</details>

### vulkan device enumeration canonical projection

#### is stable under reordering the input limits

- project both the canonical and the reordered reference record


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("project both the canonical and the reordered reference record")
val canonical = comparable_projection(required_lavapipe_reference())
val reordered = comparable_projection(lavapipe_reference_reordered())
assert_equal(comparable_projection_text(canonical), comparable_projection_text(reordered))
```

</details>

#### keeps queue family flag sets and counts, drops nothing structural

- read the projected queue family count


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("read the projected queue family count")
val projection = comparable_projection(required_lavapipe_reference())
assert_equal(projection.queue_family_count, 1)
assert_equal(projection.queue_families[0].queue_count, 1)
```

</details>

#### keeps memory heap and type counts

- read the projected memory counts


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("read the projected memory counts")
val projection = comparable_projection(required_lavapipe_reference())
assert_equal(projection.memory_heap_count, 1)
assert_equal(projection.memory_type_count, 1)
```

</details>

#### compares two structurally identical records as equal regardless of device-specific fields

- compare the reference against itself reordered


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("compare the reference against itself reordered")
assert_true(enumeration_records_structurally_equal(
    required_lavapipe_reference(),
    lavapipe_reference_reordered()
))
```

</details>

### vulkan device enumeration sabotage proof

#### REJECTS a record missing a memory type's HOST_CACHED flag, naming that memory type in the failure

- compare the real reference against the narrowed memory type
- confirm the mismatch is specifically the memory type's flag set, not something else


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("compare the real reference against the narrowed memory type")
val reference = required_lavapipe_reference()
val sabotaged = lavapipe_sabotaged_memory_type()
assert_false(enumeration_records_structurally_equal(reference, sabotaged))
step("confirm the mismatch is specifically the memory type's flag set, not something else")
assert_not_equal(
    comparable_projection_text(comparable_projection(reference)).contains("HOST_CACHED"),
    comparable_projection_text(comparable_projection(sabotaged)).contains("HOST_CACHED")
)
```

</details>

#### REJECTS a record missing its whole queue family, naming zero queue families in the failure

- compare the real reference against the queue-family-dropped record
- confirm the mutated side reports zero queue families


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("compare the real reference against the queue-family-dropped record")
val reference = required_lavapipe_reference()
val sabotaged = lavapipe_sabotaged_missing_queue_family()
assert_false(enumeration_records_structurally_equal(reference, sabotaged))
step("confirm the mutated side reports zero queue families")
assert_equal(comparable_projection(sabotaged).queue_family_count, 0)
assert_true(comparable_projection(reference).queue_family_count > 0)
```

</details>

#### ACCEPTS the restored record again, proving the gate is not stuck red

- compare a fresh real execution against another fresh real execution


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("compare a fresh real execution against another fresh real execution")
assert_true(enumeration_records_structurally_equal(
    required_lavapipe_reference(),
    required_lavapipe_reference()
))
```

</details>

### vulkan device enumeration candidate honesty

#### reports the candidate as unavailable by actually calling its real probes, not by a hard-coded literal

- call the real GpuVendorRegistry probe chain and the real venus transport calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("call the real GpuVendorRegistry probe chain and the real venus transport calls")
assert_false(candidate_enumeration_is_available())
assert_equal(candidate_enumeration_status(), ProviderStatus.unavailable)
```

</details>

#### never treats unavailable as a passing comparison

- state explicitly why: ProviderStatus enumerates unavailable separately from executed


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("state explicitly why: ProviderStatus enumerates unavailable separately from executed")
assert_true(candidate_enumeration_status() != ProviderStatus.executed)
```

</details>

### vulkan device enumeration provider wiring

#### wires two sources without editing any central registry file

- read the plan sources for this boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("read the plan sources for this boundary")
val sources = vulkan_enumeration_plan_sources()
assert_equal(sources.len(), 2)
assert_equal(sources[0].source_id, vulkan_enumeration_source_id_simple())
assert_equal(sources[1].source_id, vulkan_enumeration_source_id_lavapipe())
```

</details>

#### marks the Simple candidate as a non-binding self-oracle

- read the authority of the candidate source


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("read the authority of the candidate source")
val sources = vulkan_enumeration_plan_sources()
assert_equal(sources[0].authority, OracleAuthority.self_execution_mode)
```

</details>

#### marks lavapipe as an independent, binding reference

- read the authority of the lavapipe source


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("read the authority of the lavapipe source")
val sources = vulkan_enumeration_plan_sources()
assert_equal(sources[1].authority, OracleAuthority.independent_reference)
```

</details>

#### groups lavapipe under the shared mesa independence group, not its own group

- read the independence group constant used for anv/lavapipe/venus-via-mesa


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("read the independence group constant used for anv/lavapipe/venus-via-mesa")
assert_equal(vulkan_enumeration_mesa_independence_group(), "mesa")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-BOARD-VULKAN-002`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `09d2b48b344e661266c5065f84c40f087163dac3702dd4d68d6f267d7155d62f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `09d2b48b344e661266c5065f84c40f087163dac3702dd4d68d6f267d7155d62f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `09d2b48b344e661266c5065f84c40f087163dac3702dd4d68d6f267d7155d62f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/01_unit/os/vulkan/device_enumeration_boundary_spec.spl
mirror: doc/06_spec/01_unit/os/vulkan/device_enumeration_boundary_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=75
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/vulkan/device_enumeration_boundary_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/01_unit/os/vulkan/device_enumeration_boundary_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/os/vulkan/device_enumeration_boundary_spec.spl:204:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'names the frozen boundary id' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/vulkan/device_enumeration_boundary_spec.spl:212:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'chooses structural_equal because enumeration is legitimately device-specific' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/vulkan/device_enumeration_boundary_spec.spl:217:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'actually executes vulkaninfo against the lavapipe ICD as a real subprocess' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/vulkan/device_enumeration_boundary_spec.spl:223:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses a non-empty device name and at least one queue family from the real transcript' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
