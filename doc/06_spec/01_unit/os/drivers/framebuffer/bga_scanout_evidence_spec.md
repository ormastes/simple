# Bga Scanout Evidence Specification

> Tests covering BGA scanout evidence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bga Scanout Evidence Specification

## Scenarios

### BGA scanout evidence

#### uses QEMU's aligned word data port and retains hardware readback

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses QEMU's aligned word data port and retains hardware readback


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("uses QEMU's aligned word data port and retains hardware readback")
val source = file_read("src/os/drivers/framebuffer/bga_init.spl")
expect(source).to_contain("port_outw(0x01D0, value)")
expect(source).to_contain("port_inw(0x01D0)")
expect(source).to_contain("val active_width = bga_read(0x01)")
expect(source).to_contain("val active_height = bga_read(0x02)")
expect(source.contains("port_inw(0x01CF)")).to_be(false)
```

</details>

#### prefers the discovered PCI MMIO register BAR for stdvga

- prefers the discovered PCI MMIO register BAR for stdvga


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("prefers the discovered PCI MMIO register BAR for stdvga")
val source = file_read("src/os/drivers/framebuffer/bga_init.spl")
expect(source).to_contain("pci_config_read32(0, dev, 0, 0x18)")
expect(source).to_contain("mmio_bar + 0x0500 + index.to_u64() * 2")
expect(source).to_contain("bga_mmio_read(mmio_bar, 0x01)")
expect(source).to_contain("addr: PhysAddr(addr: pci_device.framebuffer_bar)")
expect(source).to_contain("bga_mmio_read(mmio_bar, 0x01) as u32")
```

</details>

#### preserves initialized framebuffer metadata and generation

- preserves initialized framebuffer metadata and generation
   - Expected: evidence.address equals `0xFD000000`
   - Expected: evidence.width equals `1280`
   - Expected: evidence.height equals `720`
   - Expected: evidence.stride equals `5120`
   - Expected: evidence.pixel_format equals `argb8888`
   - Expected: evidence.generation equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("preserves initialized framebuffer metadata and generation")
val fb = FramebufferInfo(
    addr: PhysAddr(addr: 0xFD000000),
    width: 1280,
    height: 720,
    pitch: 5120,
    bpp: 32
)
val evidence = scanout_evidence_from_framebuffer(fb, 7)

expect(evidence.address).to_equal(0xFD000000)
expect(evidence.width).to_equal(1280)
expect(evidence.height).to_equal(720)
expect(evidence.stride).to_equal(5120)
expect(evidence.pixel_format).to_equal("argb8888")
expect(evidence.generation).to_equal(7)
```

</details>

#### maps supported BGA depths to explicit pixel formats

- maps supported BGA depths to explicit pixel formats
   - Expected: scanout_pixel_format(32) equals `argb8888`
   - Expected: scanout_pixel_format(24) equals `rgb888`
   - Expected: scanout_pixel_format(16) equals `rgb565`
   - Expected: scanout_pixel_format(8) equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("maps supported BGA depths to explicit pixel formats")
expect(scanout_pixel_format(32)).to_equal("argb8888")
expect(scanout_pixel_format(24)).to_equal("rgb888")
expect(scanout_pixel_format(16)).to_equal("rgb565")
expect(scanout_pixel_format(8)).to_equal("unknown")
```

</details>

#### derives pixel pitch from padded byte stride

- derives pixel pitch from padded byte stride
   - Expected: scanout_stride_pixels(evidence) equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("derives pixel pitch from padded byte stride")
val evidence = ScanoutEvidence(address: 4096, width: 3, height: 2, stride: 16, pixel_format: "argb8888", generation: 1)
expect(scanout_stride_pixels(evidence)).to_equal(4)
expect(scanout_evidence_is_valid(evidence)).to_be(true)
```

</details>

#### rejects incomplete, undersized, and unsupported metadata

- rejects incomplete, undersized, and unsupported metadata


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects incomplete, undersized, and unsupported metadata")
val missing_address = ScanoutEvidence(address: 0, width: 3, height: 2, stride: 16, pixel_format: "argb8888", generation: 1)
val undersized = ScanoutEvidence(address: 4096, width: 5, height: 2, stride: 16, pixel_format: "argb8888", generation: 1)
val unsupported = ScanoutEvidence(address: 4096, width: 3, height: 2, stride: 12, pixel_format: "rgb888", generation: 1)
val stale = ScanoutEvidence(address: 4096, width: 3, height: 2, stride: 12, pixel_format: "argb8888", generation: 0)

expect(scanout_evidence_is_valid(missing_address)).to_be(false)
expect(scanout_evidence_is_valid(undersized)).to_be(false)
expect(scanout_evidence_is_valid(unsupported)).to_be(false)
expect(scanout_evidence_is_valid(stale)).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/drivers/framebuffer/bga_scanout_evidence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering BGA scanout evidence.
- BGA scanout evidence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6753f6c7e16cb1250435afa8a43f489f5a0a32b5efa137057a152060fc939531`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6753f6c7e16cb1250435afa8a43f489f5a0a32b5efa137057a152060fc939531`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6753f6c7e16cb1250435afa8a43f489f5a0a32b5efa137057a152060fc939531`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **70/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/os/drivers/framebuffer/bga_scanout_evidence_spec.spl
mirror: doc/06_spec/01_unit/os/drivers/framebuffer/bga_scanout_evidence_spec.md (current)
findings: 8 blockers: 2
  narrative=100 structure=100 oracle=20
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=70; blocker cap makes effective=49
doc/06_spec/01_unit/os/drivers/framebuffer/bga_scanout_evidence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/drivers/framebuffer/bga_scanout_evidence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/drivers/framebuffer/bga_scanout_evidence_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/os/drivers/framebuffer/bga_scanout_evidence_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/drivers/framebuffer/bga_scanout_evidence_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/drivers/framebuffer/bga_scanout_evidence_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses QEMU's aligned word data port and retains hardware readback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/drivers/framebuffer/bga_scanout_evidence_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prefers the discovered PCI MMIO register BAR for stdvga' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/drivers/framebuffer/bga_scanout_evidence_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves initialized framebuffer metadata and generation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
