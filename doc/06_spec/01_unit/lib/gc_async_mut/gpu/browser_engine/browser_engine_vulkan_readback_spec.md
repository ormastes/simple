# Browser Engine Vulkan Readback Specification

> Tests covering Browser engine vulkan readback.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Engine Vulkan Readback Specification

## Scenarios

### Browser engine vulkan readback

#### renders the fixture two-tone through the software oracle on every host

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- renders the fixture two-tone through the software oracle on every host
   - Expected: oracle.len() equals `W * H`
- oracle frame has both red-dominant and white pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders the fixture two-tone through the software oracle on every host")
val oracle = simple_web_render_html_to_pixels_with_engine2d_backend(HTML, W, H, "software")
expect(oracle.len()).to_equal(W * H)
var red = 0
var white = 0
var i = 0
while i < oracle.len():
    val p = oracle[i] & 0xFFFFFFu32
    if p == 0xFFFFFFu32:
        white = white + 1
    else:
        val r = (p >> 16u32) & 0xFFu32
        val b = p & 0xFFu32
        if r > 0x80u32 and b < 0x80u32:
            red = red + 1
    i = i + 1
step("oracle frame has both red-dominant and white pixels")
expect(red).to_be_greater_than(0)
expect(white).to_be_greater_than(0)
```

</details>

#### serves an honest, oracle-exact frame when vulkan is requested

- serves an honest, oracle-exact frame when vulkan is requested
- probe-gated resolution may only yield vulkan or software
   - Expected: resolved == "vulkan" or resolved == "software" is true
   - Expected: rb.pixels.len() equals `W * H`
- vulkan resolved — provenance must be device_readback, never a cpu label
   - Expected: rb.source equals `device_readback`
   - Expected: rb.device_identity != 0 is true
- device frame matches the software oracle exactly
   - Expected: mism equals `0`
- fallback is honest: software resolution serves a cpu_mirror frame
   - Expected: rb.source equals `cpu_mirror`
   - Expected: rgb_mismatches(rb.pixels, oracle) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("serves an honest, oracle-exact frame when vulkan is requested")
val resolved = simple_web_resolved_engine2d_backend_name(W, H, "vulkan")
step("probe-gated resolution may only yield vulkan or software")
expect(resolved == "vulkan" or resolved == "software").to_equal(true)
val oracle = simple_web_render_html_to_pixels_with_engine2d_backend(HTML, W, H, "software")
val rb = simple_web_render_html_to_readback_with_engine2d_backend(HTML, W, H, "vulkan")
expect(rb.pixels.len()).to_equal(W * H)
if resolved == "vulkan":
    step("vulkan resolved — provenance must be device_readback, never a cpu label")
    expect(rb.source).to_equal("device_readback")
    expect(rb.device_identity != 0).to_equal(true)
    val mism = rgb_mismatches(rb.pixels, oracle)
    print("[probe-gpu] browser-vulkan: GPU-PROVEN — device readback served the browser frame (source={rb.source} identity={rb.device_identity} mismatches={mism}/{W * H})")
    step("device frame matches the software oracle exactly")
    expect(mism).to_equal(0)
else:
    print("[probe-gpu] browser-vulkan: GPU BRANCH SKIPPED — vulkan did not initialize on this host; software fallback exercised, this example proves NOTHING about the GPU path")
    step("fallback is honest: software resolution serves a cpu_mirror frame")
    expect(rb.source).to_equal("cpu_mirror")
    expect(rgb_mismatches(rb.pixels, oracle)).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_engine_vulkan_readback_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Browser engine vulkan readback.
- Browser engine vulkan readback

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d242ee230340b71ee7c986f57cc7ec6650b3913f83fa883520a05e24872a0629`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d242ee230340b71ee7c986f57cc7ec6650b3913f83fa883520a05e24872a0629`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d242ee230340b71ee7c986f57cc7ec6650b3913f83fa883520a05e24872a0629`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_engine_vulkan_readback_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_engine_vulkan_readback_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_engine_vulkan_readback_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_engine_vulkan_readback_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_engine_vulkan_readback_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_engine_vulkan_readback_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders the fixture two-tone through the software oracle on every host' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_engine_vulkan_readback_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'serves an honest, oracle-exact frame when vulkan is requested' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
