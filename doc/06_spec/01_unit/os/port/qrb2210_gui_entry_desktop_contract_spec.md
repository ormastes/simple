# Qrb2210 Gui Entry Desktop Contract Specification

> Tests covering UNO Q QRB2210 desktop entry contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Qrb2210 Gui Entry Desktop Contract Specification

## Scenarios

### UNO Q QRB2210 desktop entry contract

#### fails closed on every missing physical desktop owner

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- fails closed on every missing physical desktop owner


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("fails closed on every missing physical desktop owner")
val source = file_read_text(ENTRY)
expect(source).to_contain("qrb2210_native_2d_factory_admission")
expect(source).to_contain("if not admission.admitted:")
expect(source).to_contain("panic(")
expect(source).to_contain("physical-composition-root-not-bound")
```

</details>

#### does not substitute QEMU transports or a board-private renderer

- does not substitute QEMU transports or a board-private renderer


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("does not substitute QEMU transports or a board-private renderer")
val source = file_read_text(ENTRY)
expect(source.contains("arch.arm64.gui_entry_desktop")).to_be(false)
expect(source.contains("arm64.ramfb")).to_be(false)
expect(source.contains("virtio_input")).to_be(false)
expect(source.contains("virtio_snd")).to_be(false)
expect(source.contains("host_gpu_ivshmem")).to_be(false)
expect(source.contains("FramebufferDriver")).to_be(false)
expect(source.contains("QualcommBackend.create")).to_be(false)
expect(source.contains("VulkanBackend.create")).to_be(false)
expect(source.contains("UnoQNative2dEvidence(")).to_be(false)
```

</details>

#### documents the only admissible shared rendering route and receipts

- documents the only admissible shared rendering route and receipts


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("documents the only admissible shared rendering route and receipts")
val source = file_read_text(ENTRY)
expect(source).to_contain("WM -> DrawIrComposition -> Engine2D -> Qualcomm Vulkan")
expect(source).to_contain("display, window-event, and audio owners")
expect(source).to_contain("Live input, audio, font, animation")
expect(source).to_contain("Vulkan submit/fence/readback")
expect(source).to_contain("frame-capture receipts")
expect(source).to_contain("typed DRM, evdev, PCM, and Adreno owners")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/port/qrb2210_gui_entry_desktop_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering UNO Q QRB2210 desktop entry contract.
- UNO Q QRB2210 desktop entry contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bed46d8c23ad7036d2e7ad48bc27e8da18ff930f78cc0a1ae26896272d50b061`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bed46d8c23ad7036d2e7ad48bc27e8da18ff930f78cc0a1ae26896272d50b061`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bed46d8c23ad7036d2e7ad48bc27e8da18ff930f78cc0a1ae26896272d50b061`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/port/qrb2210_gui_entry_desktop_contract_spec.spl
mirror: doc/06_spec/01_unit/os/port/qrb2210_gui_entry_desktop_contract_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/01_unit/os/port/qrb2210_gui_entry_desktop_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/port/qrb2210_gui_entry_desktop_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/port/qrb2210_gui_entry_desktop_contract_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/os/port/qrb2210_gui_entry_desktop_contract_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed on every missing physical desktop owner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/port/qrb2210_gui_entry_desktop_contract_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'documents the only admissible shared rendering route and receipts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
