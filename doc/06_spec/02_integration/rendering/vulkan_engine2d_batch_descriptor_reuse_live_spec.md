# vulkan_engine2d_batch_descriptor_reuse_live_spec

> Vulkan per-pipeline descriptor reuse evidence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# vulkan_engine2d_batch_descriptor_reuse_live_spec

Vulkan per-pipeline descriptor reuse evidence.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/vulkan_engine2d_batch_descriptor_reuse_live_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Vulkan per-pipeline descriptor reuse evidence.

## Scenarios

### Vulkan Engine2D batch descriptor reuse

#### uses one descriptor per primitive pipeline in one submit

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses one descriptor per primitive pipeline in one submit
   - Expected: vulkan.pending_compute_count equals `2`
   - Expected: vulkan.pending_compute_descriptors.len() equals `256`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("uses one descriptor per primitive pipeline in one submit")
val result = Engine2D.create_with_backend_strict(16, 16, "vulkan")
if result.is_ok():
    var engine = result.unwrap()
    val before = vulkan_sffi_accepted_compute_submit_count()
    engine.clear(0xFF0000FFu32)
    engine.draw_rect_filled(2, 2, 6, 6, 0xFFFF0000u32)
    engine.draw_rect_filled(8, 8, 4, 4, 0xFFFF0000u32)
    if val Some(vulkan) = engine.vulkan_backend:
        expect(vulkan.pending_compute_count).to_equal(2)
        expect(vulkan.pending_compute_descriptors.len()).to_equal(256)
    else:
        expect(false).to_equal(true)
    engine.read_pixels_with_source()
    expect(
        vulkan_sffi_accepted_compute_submit_count() - before
    ).to_equal(1)
    engine.shutdown()
else:
    expect(result.unwrap_err().fallback_reason).to_not_equal("")
```

</details>

#### keeps thirty-two damaged image sources in one fenced submit

- keeps thirty-two damaged image sources in one fenced submit
   - Expected: vulkan.pending_compute_count equals `33`
   - Expected: false is true
   - Expected: readback.pixels.len() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("keeps thirty-two damaged image sources in one fenced submit")
val result = Engine2D.create_with_backend_strict(64, 1, "vulkan")
if result.is_ok():
    var engine = result.unwrap()
    val before = vulkan_sffi_accepted_compute_submit_count()
    engine.clear(0xFF101010u32)
    var x = 0
    while x < 32:
        engine.draw_image(x * 2, 0, 1, 1, [0xFFFF0000u32])
        x += 1
    if val Some(vulkan) = engine.vulkan_backend:
        expect(vulkan.pending_compute_count).to_equal(33)
        expect(vulkan.pending_compute_sources[32]).to_be_greater_than(0)
    else:
        expect(false).to_equal(true)
    val readback = engine.read_pixels_with_source()
    expect(readback.pixels.len()).to_equal(64)
    expect(
        vulkan_sffi_accepted_compute_submit_count() - before
    ).to_equal(1)
    engine.shutdown()
else:
    expect(result.unwrap_err().fallback_reason).to_not_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `c86202e00e21a6bad88c028fda5b0a6e7ef5bf01ff8f4cca3bed849e876f40df`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c86202e00e21a6bad88c028fda5b0a6e7ef5bf01ff8f4cca3bed849e876f40df`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c86202e00e21a6bad88c028fda5b0a6e7ef5bf01ff8f4cca3bed849e876f40df`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/02_integration/rendering/vulkan_engine2d_batch_descriptor_reuse_live_spec.spl
mirror: doc/06_spec/02_integration/rendering/vulkan_engine2d_batch_descriptor_reuse_live_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/rendering/vulkan_engine2d_batch_descriptor_reuse_live_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/rendering/vulkan_engine2d_batch_descriptor_reuse_live_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/rendering/vulkan_engine2d_batch_descriptor_reuse_live_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/rendering/vulkan_engine2d_batch_descriptor_reuse_live_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses one descriptor per primitive pipeline in one submit' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/rendering/vulkan_engine2d_batch_descriptor_reuse_live_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps thirty-two damaged image sources in one fenced submit' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
