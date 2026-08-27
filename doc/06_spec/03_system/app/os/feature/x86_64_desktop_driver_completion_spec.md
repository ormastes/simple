# X86 64 Desktop Driver Completion Specification

> Tests covering x86_64 desktop driver completion marker contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X86 64 Desktop Driver Completion Specification

## Scenarios

### x86_64 desktop driver completion marker contract

#### accepts only the complete QEMU desktop driver summary

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts only the complete QEMU desktop driver summary
   - Expected: desktop_driver_summary_accepts_complete_qemu(summary) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accepts only the complete QEMU desktop driver summary")
val summary = complete_driver_summary()
expect(desktop_driver_summary_accepts_complete_qemu(summary)).to_equal(true)
```

</details>

#### rejects resident process fallback as incomplete

- rejects resident process fallback as incomplete
   - Expected: desktop_driver_summary_accepts_complete_qemu(summary) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects resident process fallback as incomplete")
val complete = desktop_driver_summary_for_uefi_qemu(true, 5, "nvme", "bga", "framebuffer", false, "virtio-net")
val summary = desktop_driver_summary_text(complete) + "\n" +
    complete_lane_evidence() +
    "[desktop-e2e] process-backed:resident app=browser_demo pid=10737\n"
expect(desktop_driver_summary_accepts_complete_qemu(summary)).to_equal(false)
```

</details>

#### rejects false VGA acceleration claims

- rejects false VGA acceleration claims
   - Expected: desktop_driver_summary_accepts_complete_qemu(summary) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects false VGA acceleration claims")
val complete = desktop_driver_summary_for_uefi_qemu(true, 5, "nvme", "vga", "vga", true, "virtio-net")
val summary = desktop_driver_summary_text(complete) + "\n" + complete_lane_evidence()
expect(desktop_driver_summary_accepts_complete_qemu(summary)).to_equal(false)
```

</details>

#### rejects zero PCI enumeration even with later evidence

- rejects zero PCI enumeration even with later evidence
   - Expected: desktop_driver_summary_accepts_complete_qemu(summary) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects zero PCI enumeration even with later evidence")
val complete = desktop_driver_summary_for_uefi_qemu(true, 0, "nvme", "virtio-gpu", "virtio-gpu", true, "virtio-net")
val summary = desktop_driver_summary_text(complete) + "\n" + complete_lane_evidence()
expect(desktop_driver_summary_accepts_complete_qemu(summary)).to_equal(false)
```

</details>

#### rejects absent storage display dma interrupt input or network evidence

- rejects absent storage display dma interrupt input or network evidence
   - Expected: desktop_driver_summary_accepts_complete_qemu(desktop_driver_summary_text(no_storage) + "\n" + complete_lane_evidence()) is false
   - Expected: desktop_driver_summary_accepts_complete_qemu(desktop_driver_summary_text(no_display) + "\n" + complete_lane_evidence()) is false
   - Expected: desktop_driver_summary_accepts_complete_qemu(desktop_driver_summary_text(no_network) + "\n" + complete_lane_evidence()) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects absent storage display dma interrupt input or network evidence")
val no_storage = desktop_driver_summary_for_uefi_qemu(true, 5, "none", "virtio-gpu", "virtio-gpu", true, "virtio-net")
val no_display = desktop_driver_summary_for_uefi_qemu(true, 5, "nvme", "none", "none", false, "virtio-net")
val no_network = desktop_driver_summary_for_uefi_qemu(true, 5, "nvme", "virtio-gpu", "virtio-gpu", true, "unsupported")
expect(desktop_driver_summary_accepts_complete_qemu(desktop_driver_summary_text(no_storage) + "\n" + complete_lane_evidence())).to_equal(false)
expect(desktop_driver_summary_accepts_complete_qemu(desktop_driver_summary_text(no_display) + "\n" + complete_lane_evidence())).to_equal(false)
expect(desktop_driver_summary_accepts_complete_qemu(desktop_driver_summary_text(no_network) + "\n" + complete_lane_evidence())).to_equal(false)
```

</details>

#### requires all process-backed desktop app markers

- requires all process-backed desktop app markers
   - Expected: desktop_driver_summary_accepts_complete_qemu(summary) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires all process-backed desktop app markers")
val summary = complete_driver_summary().replace(
    "[desktop-e2e] process-backed:ok app=file_manager pid=15\n",
    ""
)
expect(desktop_driver_summary_accepts_complete_qemu(summary)).to_equal(false)
```

</details>

#### requires generic VFS app-read and virtio-net queue smoke evidence

- requires generic VFS app-read and virtio-net queue smoke evidence
   - Expected: desktop_driver_summary_accepts_complete_qemu(missing_vfs) is false
   - Expected: desktop_driver_summary_accepts_complete_qemu(missing_info_vfs) is false
   - Expected: desktop_driver_summary_accepts_complete_qemu(missing_rx) is false
   - Expected: desktop_driver_summary_accepts_complete_qemu(missing_bounded_smoke) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires generic VFS app-read and virtio-net queue smoke evidence")
val missing_vfs = complete_driver_summary().replace(
    "[desktop-e2e] vfs-app-read:ok source=generic-vfs path=/sys/apps/browser_demo bytes=4096\n",
    ""
)
val missing_info_vfs = complete_driver_summary().replace(
    "[desktop-e2e] vfs-app-read:ok source=generic-vfs path=/sys/apps/info bytes=4096\n",
    ""
)
val missing_rx = complete_driver_summary().replace(
    "[desktop-e2e] virtio-net:rx-queue=ok queue=0\n",
    ""
)
val missing_bounded_smoke = complete_driver_summary().replace(
    "[desktop-e2e] network-smoke:bounded ok packets=2 timeout_ms=500\n",
    ""
)
expect(desktop_driver_summary_accepts_complete_qemu(missing_vfs)).to_equal(false)
expect(desktop_driver_summary_accepts_complete_qemu(missing_info_vfs)).to_equal(false)
expect(desktop_driver_summary_accepts_complete_qemu(missing_rx)).to_equal(false)
expect(desktop_driver_summary_accepts_complete_qemu(missing_bounded_smoke)).to_equal(false)
```

</details>

#### wires the runner UEFI serial acceptance to the completion contract

- wires the runner UEFI serial acceptance to the completion contract
   - Expected: desktop_uefi_serial_accepts_completion(summary) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("wires the runner UEFI serial acceptance to the completion contract")
val summary = complete_driver_summary()
expect(desktop_uefi_serial_accepts_completion(summary)).to_equal(true)
expect(desktop_uefi_serial_accepts_completion(summary.replace(
    "[desktop-e2e] virtio-net:tx-queue=ok queue=0\n",
    ""
))).to_equal(false)
expect(desktop_uefi_required_marker_fragments()).to_contain("[desktop-e2e] network-smoke:bounded ok packets=")
```

</details>

#### rejects hidden copy and resident VFS fallbacks

- rejects hidden copy and resident VFS fallbacks
   - Expected: desktop_driver_summary_accepts_complete_qemu(hidden_copy) is false
   - Expected: desktop_driver_summary_accepts_complete_qemu(resident_vfs) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects hidden copy and resident VFS fallbacks")
val hidden_copy = complete_driver_summary() + "[desktop-e2e] dma:hidden-copy fallback=true\n"
val resident_vfs = complete_driver_summary() + "[desktop-e2e] vfs-app-read:resident path=/sys/apps/browser_demo\n"
expect(desktop_driver_summary_accepts_complete_qemu(hidden_copy)).to_equal(false)
expect(desktop_driver_summary_accepts_complete_qemu(resident_vfs)).to_equal(false)
```

</details>

#### does not treat the current direct QEMU lane as UEFI-complete

- does not treat the current direct QEMU lane as UEFI-complete
   - Expected: summary contains `boot=qemu-direct`
   - Expected: summary contains `storage=nvme`
   - Expected: desktop_driver_summary_accepts_complete_qemu(summary) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not treat the current direct QEMU lane as UEFI-complete")
val direct = desktop_driver_summary_for_qemu_direct(true)
val summary = desktop_driver_summary_text(direct) + "\n" + complete_lane_evidence()
expect(summary.contains("boot=qemu-direct")).to_equal(true)
expect(summary.contains("storage=nvme")).to_equal(true)
expect(desktop_driver_summary_accepts_complete_qemu(summary)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/os/feature/x86_64_desktop_driver_completion_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering x86_64 desktop driver completion marker contract.
- x86_64 desktop driver completion marker contract

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0c3c575dc4274b15fee50dd13d691d8976828278eb108b0de11f8bc718c598d7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0c3c575dc4274b15fee50dd13d691d8976828278eb108b0de11f8bc718c598d7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0c3c575dc4274b15fee50dd13d691d8976828278eb108b0de11f8bc718c598d7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/app/os/feature/x86_64_desktop_driver_completion_spec.spl
mirror: doc/06_spec/03_system/app/os/feature/x86_64_desktop_driver_completion_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/os/feature/x86_64_desktop_driver_completion_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/os/feature/x86_64_desktop_driver_completion_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/os/feature/x86_64_desktop_driver_completion_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts only the complete QEMU desktop driver summary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/os/feature/x86_64_desktop_driver_completion_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires all process-backed desktop app markers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/os/feature/x86_64_desktop_driver_completion_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires generic VFS app-read and virtio-net queue smoke evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
