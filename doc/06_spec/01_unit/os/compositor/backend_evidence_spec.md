# Backend Evidence Specification

> Tests covering GUI backend evidence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Evidence Specification

## Scenarios

### GUI backend evidence

#### readback status

#### accepts explicit verified readback markers

- accepts explicit verified readback markers
   - Expected: backend_readback_verified("verified") is true
   - Expected: backend_readback_verified("verified:metal-texture-readback") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts explicit verified readback markers")
expect(backend_readback_verified("verified")).to_equal(true)
expect(backend_readback_verified("verified:metal-texture-readback")).to_equal(true)
```

</details>

#### does not treat unavailable readback as verified

- does not treat unavailable readback as verified
   - Expected: backend_readback_verified("unavailable:qemu-framebuffer-write-only") is false
   - Expected: backend_readback_verified("") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not treat unavailable readback as verified")
expect(backend_readback_verified("unavailable:qemu-framebuffer-write-only")).to_equal(false)
expect(backend_readback_verified("")).to_equal(false)
```

</details>

#### claim policy

#### requires verified readback for Metal, GPU, and QEMU SIMD claims

- requires verified readback for Metal, GPU, and QEMU SIMD claims
   - Expected: backend_claim_requires_verified_readback("metal") is true
   - Expected: backend_claim_requires_verified_readback("macos_metal") is true
   - Expected: backend_claim_requires_verified_readback("qemu_framebuffer_cpu_simd") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires verified readback for Metal, GPU, and QEMU SIMD claims")
expect(backend_claim_requires_verified_readback("metal")).to_equal(true)
expect(backend_claim_requires_verified_readback("macos_metal")).to_equal(true)
expect(backend_claim_requires_verified_readback("qemu_framebuffer_cpu_simd")).to_equal(true)
```

</details>

#### does not require verified readback for explicit CPU fallback reports

- does not require verified readback for explicit CPU fallback reports
   - Expected: backend_claim_requires_verified_readback("cpu") is false
   - Expected: backend_claim_requires_verified_readback("browser_compositor_cpu_readback") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not require verified readback for explicit CPU fallback reports")
expect(backend_claim_requires_verified_readback("cpu")).to_equal(false)
expect(backend_claim_requires_verified_readback("browser_compositor_cpu_readback")).to_equal(false)
```

</details>

#### fail closed

#### fails when a fallback is reported without a fallback reason

- fails when a fallback is reported without a fallback reason
   - Expected: evidence.ok is false
   - Expected: evidence.error equals `fallback-without-reason`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails when a fallback is reported without a fallback reason")
val evidence = make_gui_backend_evidence("metal", "cpu", "", 1200, "verified:cpu-mirror")
expect(evidence.ok).to_equal(false)
expect(evidence.error).to_equal("fallback-without-reason")
```

</details>

#### allows fallback when the reason and readback status are explicit

- allows fallback when the reason and readback status are explicit
   - Expected: evidence.ok is true
   - Expected: evidence.error equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows fallback when the reason and readback status are explicit")
val evidence = make_gui_backend_evidence("metal", "cpu", "Metal probe unavailable; using CPU mirror", 1200, "verified:cpu-mirror")
expect(evidence.ok).to_equal(true)
expect(evidence.error).to_equal("")
```

</details>

#### fails a Metal claim without verified readback

- fails a Metal claim without verified readback
   - Expected: evidence.ok is false
   - Expected: evidence.error equals `verified-readback-required-for-metal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails a Metal claim without verified readback")
val evidence = make_gui_backend_evidence("metal", "metal", "", 900, "unavailable:metal-readback-not-wired")
expect(evidence.ok).to_equal(false)
expect(evidence.error).to_equal("verified-readback-required-for-metal")
```

</details>

#### fails a QEMU SIMD claim without verified readback

- fails a QEMU SIMD claim without verified readback
   - Expected: evidence.ok is false
   - Expected: evidence.error equals `verified-readback-required-for-qemu_framebuffer_cpu_simd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails a QEMU SIMD claim without verified readback")
val evidence = make_gui_backend_evidence("qemu_framebuffer_cpu_simd", "qemu_framebuffer_cpu_simd", "", 2100, "unavailable:qmp-capture-missing")
expect(evidence.ok).to_equal(false)
expect(evidence.error).to_equal("verified-readback-required-for-qemu_framebuffer_cpu_simd")
```

</details>

#### passes verified QEMU SIMD evidence

- passes verified QEMU SIMD evidence
   - Expected: evidence.ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes verified QEMU SIMD evidence")
val evidence = make_gui_backend_evidence("qemu_framebuffer_cpu_simd", "qemu_framebuffer_cpu_simd", "", 2100, "verified:qmp-screendump")
expect(evidence.ok).to_equal(true)
```

</details>

#### records all required report fields in diagnostic text

- records all required report fields in diagnostic text
   - Expected: text contains `requested=cpu`
   - Expected: text contains `selected=cpu`
   - Expected: text contains `frame_time_us=77`
   - Expected: text contains `readback=verified`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records all required report fields in diagnostic text")
val evidence = make_verified_gui_backend_evidence("cpu", "cpu", 77)
val text = evidence.diagnostic_text()
expect(text.contains("requested=cpu")).to_equal(true)
expect(text.contains("selected=cpu")).to_equal(true)
expect(text.contains("frame_time_us=77")).to_equal(true)
expect(text.contains("readback=verified")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/compositor/backend_evidence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering GUI backend evidence.
- GUI backend evidence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `f80bc755deac47d5fa36f271a2ab524263381feb38a5000eaee48fa759bc5778`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f80bc755deac47d5fa36f271a2ab524263381feb38a5000eaee48fa759bc5778`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f80bc755deac47d5fa36f271a2ab524263381feb38a5000eaee48fa759bc5778`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/compositor/backend_evidence_spec.spl
mirror: doc/06_spec/01_unit/os/compositor/backend_evidence_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/compositor/backend_evidence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/compositor/backend_evidence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/compositor/backend_evidence_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts explicit verified readback markers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/backend_evidence_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not treat unavailable readback as verified' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/backend_evidence_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires verified readback for Metal, GPU, and QEMU SIMD claims' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
