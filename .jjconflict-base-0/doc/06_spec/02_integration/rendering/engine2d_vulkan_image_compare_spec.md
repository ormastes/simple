# engine2d_vulkan_image_compare_spec

> Engine2D software-vs-Vulkan rendered-image comparison.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# engine2d_vulkan_image_compare_spec

Engine2D software-vs-Vulkan rendered-image comparison.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/engine2d_vulkan_image_compare_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Engine2D software-vs-Vulkan rendered-image comparison.

Renders the same axis-aligned scene (clear + filled rects + clip) through the
software backend and through a real Vulkan device, reads back the Vulkan
framebuffer, and compares images pixel-for-pixel. The scene deliberately uses
only rect fills and clipping so GPU rasterization is bit-exact against the
CPU reference — no circles/lines whose GPU coverage rules may differ.

Skips (with a real probe diagnostic) only when the host has no usable Vulkan
device; on this repo's CI hosts lavapipe guarantees one.

## Scenarios

### Engine2D Vulkan rendered-buffer image comparison

#### vulkan device readback vs software reference

#### renders the scene identically on Vulkan and software backends

- renders the scene identically on Vulkan and software backends
   - Expected: probe.diagnostic_text().len() > 0 is true
   - Expected: created.is_ok() is true
   - Expected: readback.source equals `device_readback`
   - Expected: readback.pixel_count equals `(W * H).to_i64()`
   - Expected: mismatch_count(readback.pixels, software) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("renders the scene identically on Vulkan and software backends")
val probe = Engine2D.probe_backend(W, H, "vulkan")
if not probe.is_ok():
    # No Vulkan device on this host — record why, pass vacuously
    # only with the diagnostic visible in the spec output.
    print("VULKAN_UNAVAILABLE diagnostic=" + probe.diagnostic_text())
    expect(probe.diagnostic_text().len() > 0).to_equal(true)
    return
val created = Engine2D.create_with_backend_strict(W, H, "vulkan")
expect(created.is_ok()).to_equal(true)
var engine = created.unwrap()
draw_compare_scene(engine)
# Read BEFORE present(): the dirty-frame path downloads pixels
# straight from the device buffer (source=device_readback);
# present() would refresh the host cache and a later read would
# return source=host_cache_after_device_present instead.
val readback = engine.read_pixels_with_source()
val software = render_software()
print("VULKAN_COMPARE source=" + readback.source +
    " pixels=" + readback.pixel_count.to_text() +
    " checksum=" + readback.checksum.to_text())
# A CPU-fallback readback would compare the software mirror with
# itself — demand pixels actually came off the device.
expect(readback.source).to_equal("device_readback")
expect(readback.pixel_count).to_equal((W * H).to_i64())
expect(mismatch_count(readback.pixels, software)).to_equal(0)
engine.shutdown()
```

</details>

#### vulkan readback is deterministic across two renders

- vulkan readback is deterministic across two renders
   - Expected: probe.diagnostic_text().len() > 0 is true
   - Expected: created.is_ok() is true
   - Expected: mismatch_count(first, second) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("vulkan readback is deterministic across two renders")
val probe = Engine2D.probe_backend(W, H, "vulkan")
if not probe.is_ok():
    print("VULKAN_UNAVAILABLE diagnostic=" + probe.diagnostic_text())
    expect(probe.diagnostic_text().len() > 0).to_equal(true)
    return
var first: [u32] = []
var second: [u32] = []
var round = 0
while round < 2:
    val created = Engine2D.create_with_backend_strict(W, H, "vulkan")
    expect(created.is_ok()).to_equal(true)
    var engine = created.unwrap()
    draw_compare_scene(engine)
    engine.present()
    if round == 0:
        first = engine.read_pixels()
    else:
        second = engine.read_pixels()
    engine.shutdown()
    round = round + 1
expect(mismatch_count(first, second)).to_equal(0)
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

- Canonical SPipe generation for source `b5def341209187b538699c57852930e7c0bc4606809f05f60939f77242e91f2e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b5def341209187b538699c57852930e7c0bc4606809f05f60939f77242e91f2e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b5def341209187b538699c57852930e7c0bc4606809f05f60939f77242e91f2e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/02_integration/rendering/engine2d_vulkan_image_compare_spec.spl
mirror: doc/06_spec/02_integration/rendering/engine2d_vulkan_image_compare_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/rendering/engine2d_vulkan_image_compare_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/rendering/engine2d_vulkan_image_compare_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/rendering/engine2d_vulkan_image_compare_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/rendering/engine2d_vulkan_image_compare_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders the scene identically on Vulkan and software backends' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/rendering/engine2d_vulkan_image_compare_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'vulkan readback is deterministic across two renders' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
