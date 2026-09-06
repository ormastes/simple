# Backend Evidence Specification

## Scenarios

### GUI backend evidence
_Backend evidence must fail closed when render reports overclaim._

#### readback status

#### accepts explicit verified readback markers

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(backend_readback_verified("verified")).to_equal(true)
expect(backend_readback_verified("verified:metal-texture-readback")).to_equal(true)
```

</details>

#### does not treat unavailable readback as verified

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(backend_readback_verified("unavailable:qemu-framebuffer-write-only")).to_equal(false)
expect(backend_readback_verified("")).to_equal(false)
```

</details>

#### claim policy

#### requires verified readback for Metal, GPU, and QEMU SIMD claims

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(backend_claim_requires_verified_readback("metal")).to_equal(true)
expect(backend_claim_requires_verified_readback("macos_metal")).to_equal(true)
expect(backend_claim_requires_verified_readback("qemu_framebuffer_cpu_simd")).to_equal(true)
```

</details>

#### does not require verified readback for explicit CPU fallback reports

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(backend_claim_requires_verified_readback("cpu")).to_equal(false)
expect(backend_claim_requires_verified_readback("browser_compositor_cpu_readback")).to_equal(false)
```

</details>

#### fail closed

#### fails when a fallback is reported without a fallback reason

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = make_gui_backend_evidence("metal", "cpu", "", 1200, "verified:cpu-mirror")
expect(evidence.ok).to_equal(false)
expect(evidence.error).to_equal("fallback-without-reason")
```

</details>

#### allows fallback when the reason and readback status are explicit

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = make_gui_backend_evidence("metal", "cpu", "Metal probe unavailable; using CPU mirror", 1200, "verified:cpu-mirror")
expect(evidence.ok).to_equal(true)
expect(evidence.error).to_equal("")
```

</details>

#### fails a Metal claim without verified readback

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = make_gui_backend_evidence("metal", "metal", "", 900, "unavailable:metal-readback-not-wired")
expect(evidence.ok).to_equal(false)
expect(evidence.error).to_equal("verified-readback-required-for-metal")
```

</details>

#### fails a QEMU SIMD claim without verified readback

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = make_gui_backend_evidence("qemu_framebuffer_cpu_simd", "qemu_framebuffer_cpu_simd", "", 2100, "unavailable:qmp-capture-missing")
expect(evidence.ok).to_equal(false)
expect(evidence.error).to_equal("verified-readback-required-for-qemu_framebuffer_cpu_simd")
```

</details>

#### passes verified QEMU SIMD evidence

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = make_gui_backend_evidence("qemu_framebuffer_cpu_simd", "qemu_framebuffer_cpu_simd", "", 2100, "verified:qmp-screendump")
expect(evidence.ok).to_equal(true)
```

</details>

#### records all required report fields in diagnostic text

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- GUI backend evidence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

