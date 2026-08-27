# WM Glass Cross-Host Evidence Requests

> Keeps Windows, Linux, x86 QEMU, and ARM QEMU work as explicit fail-closed

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# WM Glass Cross-Host Evidence Requests

Keeps Windows, Linux, x86 QEMU, and ARM QEMU work as explicit fail-closed

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/check/wm_glass_cross_host_evidence_request_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Keeps Windows, Linux, x86 QEMU, and ARM QEMU work as explicit fail-closed
requests while the current macOS source and evidence lane stays active.

This contract validates the handoff and admission vocabulary. It does not
claim that any external host has executed the requested evidence.

## Scenarios

### WM glass cross-host evidence request contract

#### keeps the current macOS lane active rather than postponing all work

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps the current macOS lane active rather than postponing all work
- Read the cross-host request ledger
- Check the current-host routing boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps the current macOS lane active rather than postponing all work")
step("Read the cross-host request ledger")
val request = cross_host_request_text()

step("Check the current-host routing boundary")
expect(request).to_contain("Current macOS lane — not postponed")
expect(request).to_contain("MAC-WM-GLASS-LOCAL-001")
expect(request).to_contain("remains active locally")
expect(request).to_contain(
    "Metal backend creation falling back to CPU remains a failure"
)
```

</details>

#### records actionable Windows and Linux host requests

- records actionable Windows and Linux host requests
- Check Windows Vulkan and SIMD ownership
- Check Linux Vulkan RenderDoc and SIMD ownership


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records actionable Windows and Linux host requests")
step("Check Windows Vulkan and SIMD ownership")
val request = cross_host_request_text()
expect(request).to_contain("FR-WM-GLASS-WIN-0001")
expect(request).to_contain(
    "check-wm-glass-windows-vulkan-evidence.shs"
)
expect(request).to_contain("pure-Simple Vulkan row")
expect(request).to_contain("x86 SIMD oracle")

step("Check Linux Vulkan RenderDoc and SIMD ownership")
expect(request).to_contain("FR-WM-GLASS-LINUX-0001")
expect(request).to_contain(
    "check-wm-glass-linux-vulkan-evidence.shs"
)
expect(request).to_contain("valid regular-file `RDOC` artifact")
expect(request).to_contain("native focus, pointer, keyboard, click")
```

</details>

#### records source-bound x86 and ARM QEMU requests

- records source-bound x86 and ARM QEMU requests
- Check the x86 QEMU rendering and event request
- Check the ARM QEMU rendering and event request


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records source-bound x86 and ARM QEMU requests")
step("Check the x86 QEMU rendering and event request")
val request = cross_host_request_text()
expect(request).to_contain("FR-WM-GLASS-X86-QEMU-0001")
expect(request).to_contain(
    "check-simpleos-x86-64-wm-render-event-evidence.shs"
)
expect(request).to_contain("SSE2 parity")
expect(request).to_contain("QMP focus/pointer/key make-break events")

step("Check the ARM QEMU rendering and event request")
expect(request).to_contain("FR-WM-GLASS-ARM-QEMU-0001")
expect(request).to_contain(
    "check-simpleos-arm64-qmp-input-evidence.shs"
)
expect(request).to_contain("NEON parity")
expect(request).to_contain("VirtIO input")
```

</details>

#### requires complete device capture and native event receipts

- requires complete device capture and native event receipts
- Inspect the common admission receipt


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires complete device capture and native event receipts")
step("Inspect the common admission receipt")
val request = cross_host_request_text()
expect(request).to_contain("source commit and dirty-state receipt")
expect(request).to_contain(
    "self-hosted pure-Simple runtime kind, version, and SHA-256"
)
expect(request).to_contain(
    "Aetheric manifest and glass-material SHA-256"
)
expect(request).to_contain("device-origin readback source")
expect(request).to_contain("CPU/SIMD oracle SHA-256")
expect(request).to_contain(
    "focus, pointer, keyboard, click, frame-commit, and damage receipts"
)
expect(request).to_contain(
    "zero skipped commands and zero unapproved fallback count"
)
```

</details>

#### keeps every external row postponed and fail closed

- keeps every external row postponed and fail closed
- Count the explicit external-host postponement markers
   - Expected: request.split(marker).len() equals `5`
- Reject fixture and fallback substitutes in the contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps every external row postponed and fail closed")
step("Count the explicit external-host postponement markers")
val request = cross_host_request_text()
val marker = "**Status:** postponed-external-host"
expect(request.split(marker).len()).to_equal(5)

step("Reject fixture and fallback substitutes in the contract")
expect(request).to_contain(
    "Generic clear/fill, synthetic events, stale captures"
)
expect(request).to_contain(
    "Any absent, stale, malformed, synthetic, or mismatched field"
)
expect(request).to_contain(
    "They are required rows, not exclusions and not PASS"
)
```

</details>

#### registers every request in the canonical feature database

- registers every request in the canonical feature database
- Read the canonical feature registry
- Check each cross-host request identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("registers every request in the canonical feature database")
step("Read the canonical feature registry")
val feature_db = file_read(
    "doc/08_tracking/feature/feature_db.sdn"
)

step("Check each cross-host request identity")
expect(feature_db).to_contain("\"FR-WM-GLASS-WIN-0001\"")
expect(feature_db).to_contain("\"FR-WM-GLASS-LINUX-0001\"")
expect(feature_db).to_contain("\"FR-WM-GLASS-X86-QEMU-0001\"")
expect(feature_db).to_contain("\"FR-WM-GLASS-ARM-QEMU-0001\"")
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-002`
- `REQ-003`
- `REQ-004`
- `REQ-005`
- `REQ-006`
- `REQ-007`
- `REQ-008`
- `REQ-009`
- `REQ-010`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bc109a7f6d247f235536bd049ca9b99cf0d7b895d83a847a7f9c16d0a76f760f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bc109a7f6d247f235536bd049ca9b99cf0d7b895d83a847a7f9c16d0a76f760f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bc109a7f6d247f235536bd049ca9b99cf0d7b895d83a847a7f9c16d0a76f760f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/check/wm_glass_cross_host_evidence_request_spec.spl
mirror: doc/06_spec/03_system/check/wm_glass_cross_host_evidence_request_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=90
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/03_system/check/wm_glass_cross_host_evidence_request_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/wm_glass_cross_host_evidence_request_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/wm_glass_cross_host_evidence_request_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/check/wm_glass_cross_host_evidence_request_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 9 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/check/wm_glass_cross_host_evidence_request_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the current macOS lane active rather than postponing all work' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/wm_glass_cross_host_evidence_request_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records actionable Windows and Linux host requests' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/wm_glass_cross_host_evidence_request_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records source-bound x86 and ARM QEMU requests' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
