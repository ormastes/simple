# Engine2D configured-font offload fallback (system lane)

> Proves, through a REAL compiled binary, that Engine2D's configured-font

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2D configured-font offload fallback (system lane)

Proves, through a REAL compiled binary, that Engine2D's configured-font

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | In Progress — fail-closed, blocked on a qualified pure-Simple runtime |
| Requirements | doc/02_requirements/feature/feature.md |
| Plan | doc/03_plan/sys_test/engine2d_font_offload_fallback_system_lane.md |
| Design | doc/07_guide/ui/engine2d_font_offload_fallback.md |
| Source | `test/03_system/lib/gpu/engine2d/engine2d_font_offload_fallback_system_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Proves, through a REAL compiled binary, that Engine2D's configured-font
execution walks its documented backend preference order, records one ledger
entry per attempt, and always lands on a surface that was actually painted.
Audience: anyone changing `Engine2D` backend routing or the font offload lane.

## Scope and Preconditions

Requires an admitted pure-Simple runtime (`SIMPLE_QUALIFIED_RUNTIME`). The Rust
bootstrap seed is explicitly NOT acceptable evidence for this lane. Without an
admitted runtime these scenarios FAIL — they never skip and never pass
vacuously.

The in-process shape of this behaviour is already covered by
`test/01_unit/lib/gpu/engine2d/font_runtime_config_spec.spl`. This lane exists
for what a unit spec structurally cannot observe: the lowering + native runtime
seam, which is where the routing bug this lane fences actually bites.

## Primary Workflow

Admit a runtime, native-build `test/fixtures/engine2d_font_offload_fallback/`,
execute it, and validate the emitted attempt ledger against the documented
preference order.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Attempt ledger | `font_execution_attempts()` — one `backend:outcome` entry per target tried, in order |
| Fallthrough | An attached backend that cannot service the batch records `failed`/`unavailable` and yields to the next candidate |
| Terminal cpu | `cpu:success` is the documented last resort and must terminate the ledger |

## Related Specifications

- [Bitmap font offload](../../../../01_unit/lib/gpu/engine2d/bitmap_font_offload_spec.spl) — in-process offload shape
- [Vulkan font route](../../../../01_unit/lib/gc_async_mut/gpu/engine2d/engine_vulkan_font_route_spec.spl) — uninitialized-backend fallthrough

## Evidence and Provenance

Fence for the routing repair landed in `b10f1b4309c`. No runtime evidence has
been produced for this lane as of 2026-08-16: no qualified pure-Simple runtime
exists on the reference machine (fleet sweep of 1099 binary instances, 19 unique
by md5, all five self-hosted artifacts non-functional). Tracked in
`doc/08_tracking/bug/stage3_native_build_segv_two_distinct_faults_tagged_value_seam_2026-08-11.md`.

## Recovery and Troubleshooting

A failure naming `no qualified pure-Simple runtime admitted` is the toolchain
blocker, not a defect in Engine2D. A failure naming
`failed to native-build` means the admitted runtime cannot compile at all —
repair the compiler before reading anything into the assertions below.

## Compatibility and Limitations

Asserts routing and the attempt ledger only. Makes no claim about glyph raster
correctness, GPU residency, presentation, or performance.

## Scenarios

### Engine2D configured-font offload fallback

#### reports the drawn text as painted after falling through to cpu

- reports the drawn text as painted after falling through to cpu
- Admit a pure-Simple runtime and native-build the fallback probe
- Execute the probe
- Verify the suggested-policy draw reports success
   - Expected: field(output, "suggested_drew") equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports the drawn text as painted after falling through to cpu")
step("Admit a pure-Simple runtime and native-build the fallback probe")
val probe = build_fallback_probe()

step("Execute the probe")
val output = run_probe(probe)

step("Verify the suggested-policy draw reports success")
expect(field(output, "suggested_drew")).to_equal("true")
```

</details>

#### records one ledger entry per attempted backend, in preference order

- reports the drawn text as painted after falling through to cpu
- Admit a pure-Simple runtime and native-build the fallback probe
- Execute the probe
- Verify the suggested-policy draw reports success
   - Expected: field(output, "suggested_drew") equals `true`
- records one ledger entry per attempted backend, in preference order
- Admit a pure-Simple runtime and native-build the fallback probe
- Execute the probe
- Verify the attempt ledger matches the documented preference order
   - Expected: field(output, "suggested_attempts") equals `EXPECTED_ATTEMPTS`
- Verify the ledger terminates on the cpu last resort


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports the drawn text as painted after falling through to cpu")
step("Admit a pure-Simple runtime and native-build the fallback probe")
val probe = build_fallback_probe()

step("Execute the probe")
val output = run_probe(probe)

step("Verify the suggested-policy draw reports success")
expect(field(output, "suggested_drew")).to_equal("true")

# @req REQ-SSPEC-SYSTEM
step("records one ledger entry per attempted backend, in preference order")
step("Admit a pure-Simple runtime and native-build the fallback probe")
val probe = build_fallback_probe()

step("Execute the probe")
val output = run_probe(probe)

step("Verify the attempt ledger matches the documented preference order")
expect(field(output, "suggested_attempts")).to_equal(EXPECTED_ATTEMPTS)

step("Verify the ledger terminates on the cpu last resort")
expect(field(output, "suggested_attempts").ends_with("cpu:success")).to_be(true)
```

</details>

#### walks the same order under the preferred policy

- reports the drawn text as painted after falling through to cpu
- Admit a pure-Simple runtime and native-build the fallback probe
- Execute the probe
- Verify the suggested-policy draw reports success
   - Expected: field(output, "suggested_drew") equals `true`
- walks the same order under the preferred policy
- Admit a pure-Simple runtime and native-build the fallback probe
- Execute the probe
- Verify the preferred-policy draw also reports success
   - Expected: field(output, "preferred_drew") equals `true`
- Verify the preferred-policy ledger matches the same order
   - Expected: field(output, "preferred_attempts") equals `EXPECTED_ATTEMPTS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports the drawn text as painted after falling through to cpu")
step("Admit a pure-Simple runtime and native-build the fallback probe")
val probe = build_fallback_probe()

step("Execute the probe")
val output = run_probe(probe)

step("Verify the suggested-policy draw reports success")
expect(field(output, "suggested_drew")).to_equal("true")

# @req REQ-SSPEC-SYSTEM
step("walks the same order under the preferred policy")
step("Admit a pure-Simple runtime and native-build the fallback probe")
val probe = build_fallback_probe()

step("Execute the probe")
val output = run_probe(probe)

step("Verify the preferred-policy draw also reports success")
expect(field(output, "preferred_drew")).to_equal("true")

step("Verify the preferred-policy ledger matches the same order")
expect(field(output, "preferred_attempts")).to_equal(EXPECTED_ATTEMPTS)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/feature.md`
- **Plan:** `doc/03_plan/sys_test/engine2d_font_offload_fallback_system_lane.md`
- **Design:** `doc/07_guide/ui/engine2d_font_offload_fallback.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b3f2f993231e9f417e68f9c456576ff3943c465f3e220c61a01cb2c634025d29`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b3f2f993231e9f417e68f9c456576ff3943c465f3e220c61a01cb2c634025d29`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b3f2f993231e9f417e68f9c456576ff3943c465f3e220c61a01cb2c634025d29`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/lib/gpu/engine2d/engine2d_font_offload_fallback_system_spec.spl
mirror: doc/06_spec/03_system/lib/gpu/engine2d/engine2d_font_offload_fallback_system_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=90
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/lib/gpu/engine2d/engine2d_font_offload_fallback_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/03_system/lib/gpu/engine2d/engine2d_font_offload_fallback_system_spec.spl:127:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports the drawn text as painted after falling through to cpu' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/lib/gpu/engine2d/engine2d_font_offload_fallback_system_spec.spl:141:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records one ledger entry per attempted backend, in preference order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/lib/gpu/engine2d/engine2d_font_offload_fallback_system_spec.spl:158:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'walks the same order under the preferred policy' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
