# Host Vulkan renderer against the software ICD (lavapipe) — reach, clear, read back

> The board-Vulkan effort proved SPIR-V validation with `spirv-val` but never

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Host Vulkan renderer against the software ICD (lavapipe) — reach, clear, read back

The board-Vulkan effort proved SPIR-V validation with `spirv-val` but never

## At a Glance

| Field | Value |
|-------|-------|
| Category | Infrastructure |
| Status | Active |
| Design | doc/03_plan/infra/counterpart/simple_counterparts_compare_test_two_track_plan_2026-08-11.md |
| Source | `test/01_unit/infra/counterpart/host_vulkan_lavapipe_compare_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

The board-Vulkan effort proved SPIR-V validation with `spirv-val` but never
achieved a device submit and readback: there is no GPU on this host and no
working QEMU GPU device model. The path nobody had tried is the one this
scenario exercises — Simple's **host** Vulkan code against Mesa **lavapipe**, a
pure-software ICD that needs no GPU whatsoever.

Two questions are settled here, and they have different answers:

1. **Does Simple's host Vulkan code actually reach lavapipe?** Yes. This spec
   proves it by asserting on the device string the driver really returned.
2. **Can it clear an offscreen image and read the pixels back?** Not on the
   currently deployed binary, and this spec proves *that* honestly too — as a
   real `ProviderStatus.unavailable` naming the stage that failed, never as a
   silent skip and never as a fabricated pixel buffer.

## Scope and Preconditions

Requires `/usr/share/vulkan/icd.d/lvp_icd.json` and `libvulkan_lvp.so` (Mesa
lavapipe) installed. The provider pins the ICD itself via `VK_DRIVER_FILES`
before instance creation, so this scenario does not depend on ambient
environment: the bogus-ICD scenario below re-pins to a path that does not exist
and observes the loader genuinely failing.

## Primary Workflow

Pin the lavapipe ICD, initialise Vulkan, select device 0, read its name, then
attempt a 64x64 RGBA8 offscreen clear to a whole-byte color and read the pixels
back off the device.

## Key Concepts

| Concept | Description |
|---------|-------------|
| lavapipe | Mesa's software Vulkan ICD (`llvmpipe` device) — no GPU required |
| `VK_DRIVER_FILES` | Loader variable naming the ICD manifest; read at instance creation |
| `image_exact` | Comparison relation for a pure clear: no filtering, blending, or gamma, so no tolerance is warranted |
| `ProviderStatus.unavailable` | Fail-closed verdict; a run that cannot execute is rejected, never passed |

## Related Specifications

- [Frozen counterpart contracts](../../../../src/lib/common/spec/evidence/counterpart/model.spl)
- [Host Vulkan SFFI surface](../../../../src/lib/nogc_sync_mut/io/vulkan_sffi.spl)

## Evidence and Provenance

Every device string asserted below is whatever `rt_vulkan_device_name(0)`
actually returned through the pinned ICD at run time. No device name, pixel
value, or handle in this file is a literal standing in for a measurement. The
one literal is the substring `llvmpipe`, which is the *claim under test* — that
the pinned software driver, and not some other driver, is the one that answered.

## Recovery and Troubleshooting

`unavailable` with detail `graphics unavailable: ...` means the deployed binary
was built without the runtime `vulkan` cargo feature, so the
`#[cfg(not(feature = "vulkan"))]` bodies in
`src/compiler_rust/runtime/src/vulkan_graphics_runtime_graphics.rs` are linked
and return 0 while ignoring their arguments. Device enumeration still works
because it is served by the ungated `ash` handlers in
`src/compiler_rust/compiler/src/interpreter_extern/gpu.rs`. Rebuild the seed
with `--features vulkan` to make the pixel comparison live; the provider needs
no edit. Full record:
`doc/08_tracking/bug/host_vulkan_lavapipe_graphics_entry_points_stubbed_without_vulkan_feature_2026-08-11.md`

`unavailable` with detail `vulkan init failed for ICD` means lavapipe is not
installed at the expected path — install `mesa-vulkan-drivers`.

## Scenarios

### Host Vulkan renderer against the lavapipe software ICD

#### reaches a real software Vulkan device when the lavapipe ICD is pinned

- reaches a real software Vulkan device when the lavapipe ICD is pinned
- Pin VK_DRIVER_FILES to the lavapipe ICD manifest and initialise Vulkan in-process
- Confirm the driver answered with a real device string, not an empty or placeholder one
- Confirm it is the SOFTWARE driver that answered — the claim under test


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("reaches a real software Vulkan device when the lavapipe ICD is pinned")
step("Pin VK_DRIVER_FILES to the lavapipe ICD manifest and initialise Vulkan in-process")
val device_name = host_vulkan_probe_device_name(LAVAPIPE_ICD_PATH)
step("Confirm the driver answered with a real device string, not an empty or placeholder one")
assert_true(device_name != "")
assert_true(device_name != "0")
step("Confirm it is the SOFTWARE driver that answered — the claim under test")
assert_true(device_name.contains("llvmpipe"))
```

</details>

#### reports unavailable and reaches no device when the pinned ICD does not exist

- reports unavailable and reaches no device when the pinned ICD does not exist
- Re-pin VK_DRIVER_FILES to a manifest path that is not present on this host
- Confirm the loader genuinely failed rather than falling back to another driver


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("reports unavailable and reaches no device when the pinned ICD does not exist")
step("Re-pin VK_DRIVER_FILES to a manifest path that is not present on this host")
val device_name = host_vulkan_probe_device_name(BOGUS_ICD)
step("Confirm the loader genuinely failed rather than falling back to another driver")
assert_equal(device_name, "")
```

</details>

#### rejects the run as unavailable when the pinned ICD does not exist, never faking pixels

- rejects the run as unavailable when the pinned ICD does not exist, never faking pixels
- Attempt a full clear and readback through a bogus ICD
- Confirm the run is rejected fail-closed, with no pixels and no device string invented


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("rejects the run as unavailable when the pinned ICD does not exist, never faking pixels")
step("Attempt a full clear and readback through a bogus ICD")
val outcome = host_vulkan_clear_readback(BOGUS_ICD, TILE, TILE, CLEAR_R, CLEAR_G, CLEAR_B, CLEAR_A)
step("Confirm the run is rejected fail-closed, with no pixels and no device string invented")
assert_equal(outcome.status, ProviderStatus.unavailable)
assert_false(outcome.matched)
assert_equal(outcome.readback_bytes, 0)
assert_equal(outcome.device_name, "")
assert_false(outcome.device_handle_valid)
```

</details>

#### records image_exact as the comparison relation for a pure clear

- records image_exact as the comparison relation for a pure clear
- Attempt the clear through the lavapipe ICD
- A clear applies no filtering, blending, or gamma, so the relation must be exact
- Confirm the requested color is carried through unmodified for the comparison


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("records image_exact as the comparison relation for a pure clear")
step("Attempt the clear through the lavapipe ICD")
val outcome = host_vulkan_clear_readback(LAVAPIPE_ICD_PATH, TILE, TILE, CLEAR_R, CLEAR_G, CLEAR_B, CLEAR_A)
step("A clear applies no filtering, blending, or gamma, so the relation must be exact")
assert_equal(outcome.relation, CounterpartRelation.image_exact)
step("Confirm the requested color is carried through unmodified for the comparison")
assert_equal(outcome.requested_rgba.0, CLEAR_R)
assert_equal(outcome.requested_rgba.1, CLEAR_G)
assert_equal(outcome.requested_rgba.2, CLEAR_B)
assert_equal(outcome.requested_rgba.3, CLEAR_A)
```

</details>

#### either reads back every pixel equal to the requested clear color, or reports the exact stage that was unavailable

- either reads back every pixel equal to the requested clear color, or reports the exact stage that was unavailable
- Pin the lavapipe ICD and attempt a 64x64 RGBA8 clear plus device readback
- The device itself must have been reached either way — this is the proven half
- Executed: every readback pixel must equal the requested RGBA exactly
- Not executed: the verdict must be fail-closed unavailable naming the failing stage
- And no pixel data may be reported at all


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("either reads back every pixel equal to the requested clear color, or reports the exact stage that was unavailable")
step("Pin the lavapipe ICD and attempt a 64x64 RGBA8 clear plus device readback")
val outcome = host_vulkan_clear_readback(LAVAPIPE_ICD_PATH, TILE, TILE, CLEAR_R, CLEAR_G, CLEAR_B, CLEAR_A)
step("The device itself must have been reached either way — this is the proven half")
assert_true(outcome.device_name.contains("llvmpipe"))
if outcome.status == ProviderStatus.executed:
    step("Executed: every readback pixel must equal the requested RGBA exactly")
    assert_equal(outcome.readback_bytes, TILE * TILE * 4)
    assert_true(outcome.pixels_uniform)
    assert_equal(outcome.observed_rgba.0, CLEAR_R)
    assert_equal(outcome.observed_rgba.1, CLEAR_G)
    assert_equal(outcome.observed_rgba.2, CLEAR_B)
    assert_equal(outcome.observed_rgba.3, CLEAR_A)
    assert_true(outcome.matched)
else:
    step("Not executed: the verdict must be fail-closed unavailable naming the failing stage")
    assert_equal(outcome.status, ProviderStatus.unavailable)
    assert_false(outcome.matched)
    assert_true(outcome.detail.starts_with("graphics unavailable"))
    step("And no pixel data may be reported at all")
    assert_equal(outcome.readback_bytes, 0)
    assert_equal(outcome.observed_rgba.0, -1)
```

</details>

#### goes RED when the expected clear color is sabotaged, naming the mismatch

- goes RED when the expected clear color is sabotaged, naming the mismatch
- Request one clear color but compare the readback against a different one — the sabotage check
- The sabotage must be visible as an altered request, never silently absorbed
- Executed: the comparator must report the mismatch rather than passing vacuously
- Unavailable: the sabotage cannot be evaluated, and the run must still be rejected
- Restore: the sabotaged value above is a local literal, never written back to CLEAR_G


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("goes RED when the expected clear color is sabotaged, naming the mismatch")
step("Request one clear color but compare the readback against a different one — the sabotage check")
val sabotaged_g: i64 = CLEAR_G + 1
val outcome = host_vulkan_clear_readback(LAVAPIPE_ICD_PATH, TILE, TILE, CLEAR_R, sabotaged_g, CLEAR_B, CLEAR_A)
step("The sabotage must be visible as an altered request, never silently absorbed")
assert_equal(outcome.requested_rgba.1, sabotaged_g)
assert_not_equal(outcome.requested_rgba.1, CLEAR_G)
if outcome.status == ProviderStatus.executed:
    step("Executed: the comparator must report the mismatch rather than passing vacuously")
    assert_false(outcome.matched)
    assert_true(outcome.detail.starts_with("pixel MISMATCH"))
else:
    step("Unavailable: the sabotage cannot be evaluated, and the run must still be rejected")
    assert_equal(outcome.status, ProviderStatus.unavailable)
    assert_false(outcome.matched)
step("Restore: the sabotaged value above is a local literal, never written back to CLEAR_G")
assert_equal(CLEAR_G, 128)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** `doc/03_plan/infra/counterpart/simple_counterparts_compare_test_two_track_plan_2026-08-11.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-COUNTERPART-HOSTVK-001`
- `REQ-SSPEC-INFRA`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bee716e61c1b2b6595c76a682883ec9384ca31c7a77da0ae3056fe74da306829`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bee716e61c1b2b6595c76a682883ec9384ca31c7a77da0ae3056fe74da306829`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bee716e61c1b2b6595c76a682883ec9384ca31c7a77da0ae3056fe74da306829`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/infra/counterpart/host_vulkan_lavapipe_compare_spec.spl
mirror: doc/06_spec/01_unit/infra/counterpart/host_vulkan_lavapipe_compare_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/infra/counterpart/host_vulkan_lavapipe_compare_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/infra/counterpart/host_vulkan_lavapipe_compare_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/infra/counterpart/host_vulkan_lavapipe_compare_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/infra/counterpart/host_vulkan_lavapipe_compare_spec.spl:115:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reaches a real software Vulkan device when the lavapipe ICD is pinned' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/infra/counterpart/host_vulkan_lavapipe_compare_spec.spl:126:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports unavailable and reaches no device when the pinned ICD does not exist' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/infra/counterpart/host_vulkan_lavapipe_compare_spec.spl:134:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects the run as unavailable when the pinned ICD does not exist, never faking pixels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
