# Theme Service Notification Contract Specification

> Tests covering ThemeService notification transport contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Theme Service Notification Contract Specification

## Scenarios

### ThemeService notification transport contract

#### fails until valid theme changes install one snapshot and notify IPC subscribers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- fails until valid theme changes install one snapshot and notify IPC subscribers


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fails until valid theme changes install one snapshot and notify IPC subscribers")
val service = file_read("src/os/services/theme/theme_service.spl")
val ipc_ports = file_read("src/os/kernel/ipc/ports.spl")

expect(service).to_contain("subscribers: [u64]")
expect(service).to_contain("me _notify_all()")
expect(ipc_ports).to_contain("send_fn: fn(IpcMessage) -> i64")
expect(service.contains("IpcOutputPort")).to_be(false)
expect(service.contains("send_fn")).to_be(false)

fail("ThemeService has subscriber port ids but no notification transport; see doc/08_tracking/bug/theme_service_notification_transport_contract_2026-07-24.md")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/wm/theme_service_notification_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ThemeService notification transport contract.
- ThemeService notification transport contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-7`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3c4e41fa81aeb9c10566058a4cf476473a790871c67f71d3d524c61ebc352999`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3c4e41fa81aeb9c10566058a4cf476473a790871c67f71d3d524c61ebc352999`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3c4e41fa81aeb9c10566058a4cf476473a790871c67f71d3d524c61ebc352999`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/os/wm/theme_service_notification_contract_spec.spl
mirror: doc/06_spec/03_system/os/wm/theme_service_notification_contract_spec.md (current)
findings: 4 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=89; blocker cap makes effective=49
doc/06_spec/03_system/os/wm/theme_service_notification_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/wm/theme_service_notification_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/wm/theme_service_notification_contract_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/os/wm/theme_service_notification_contract_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails until valid theme changes install one snapshot and notify IPC subscribers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
