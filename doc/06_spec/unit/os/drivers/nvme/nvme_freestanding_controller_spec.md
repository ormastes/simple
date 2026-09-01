# Nvme Freestanding Controller Specification

> Tests covering freestanding NVMe controller resources.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nvme Freestanding Controller Specification

## Scenarios

### freestanding NVMe controller resources

#### builds system-driver controller evidence without hosted syscalls

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- builds system-driver controller evidence without hosted syscalls
   - Expected: missing_probe.driver_placement equals `system-driver`
   - Expected: missing_probe.grant_kind equals `kernel-owned-resource`
   - Expected: missing_probe.namespace_mode equals `system-kernel-namespace`
   - Expected: nvme_transfer_readiness_reason(missing_probe) equals `missing-nvme-completion`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds system-driver controller evidence without hosted syscalls")
val resources = _system_resources()
val controller = nvme_freestanding_controller_from_resources(resources).unwrap()
val missing_probe = nvme_freestanding_transfer_evidence(controller, false, false, false, false)

expect(missing_probe.driver_placement).to_equal("system-driver")
expect(missing_probe.grant_kind).to_equal("kernel-owned-resource")
expect(missing_probe.namespace_mode).to_equal("system-kernel-namespace")
expect(nvme_transfer_readiness_reason(missing_probe)).to_equal("missing-nvme-completion")
```

</details>

#### only reports ready after actual completion and reversible sector probes are supplied

- only reports ready after actual completion and reversible sector probes are supplied
   - Expected: nvme_sector_probe_reason(probe) equals `ready`
   - Expected: nvme_transfer_readiness_reason(ready) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("only reports ready after actual completion and reversible sector probes are supplied")
val controller = nvme_freestanding_controller_from_resources(_system_resources()).unwrap()
val probe = nvme_sector_probe_result(0u64, 512u64, 0u32, true, true, true, true)
val ready = nvme_freestanding_transfer_evidence_from_probe(controller, probe)

expect(nvme_sector_probe_reason(probe)).to_equal("ready")
expect(nvme_transfer_readiness_reason(ready)).to_equal("ready")
```

</details>

#### rejects probe evidence that bypasses shared transfer logic

- rejects probe evidence that bypasses shared transfer logic
   - Expected: nvme_sector_probe_reason(probe) equals `nvme-sector-probe-not-shared-transfer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects probe evidence that bypasses shared transfer logic")
val controller = nvme_freestanding_controller_from_resources(_system_resources()).unwrap()
val probe = nvme_sector_probe_result(0u64, 512u64, 0u32, true, true, true, false)
val evidence = nvme_freestanding_transfer_evidence_from_probe(controller, probe)

expect(nvme_sector_probe_reason(probe)).to_equal("nvme-sector-probe-not-shared-transfer")
expect(nvme_transfer_readiness_reason(evidence)).to_contain("missing-common-driver-logic")
```

</details>

#### rejects invalid controller resources before transfer evidence can be built

- rejects invalid controller resources before transfer evidence can be built
   - Expected: nvme_freestanding_controller_resource_reason(resources) equals `nvme-freestanding-admin-qid-not-zero`
   - Expected: nvme_freestanding_controller_resource_reason(resources) equals `nvme-freestanding-io-qid-zero`
   - Expected: nvme_freestanding_controller_from_resources(resources).unwrap_err() equals `nvme-freestanding-dma-not-isolated`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid controller resources before transfer evidence can be built")
var resources = _system_resources()
resources.admin = _queue(1u16, 0x200000u64)
expect(nvme_freestanding_controller_resource_reason(resources)).to_equal("nvme-freestanding-admin-qid-not-zero")

resources = _system_resources()
resources.io = _queue(0u16, 0x220000u64)
expect(nvme_freestanding_controller_resource_reason(resources)).to_equal("nvme-freestanding-io-qid-zero")

resources = _system_resources()
resources.dma_isolated = false
expect(nvme_freestanding_controller_from_resources(resources).unwrap_err()).to_equal("nvme-freestanding-dma-not-isolated")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/drivers/nvme/nvme_freestanding_controller_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering freestanding NVMe controller resources.
- freestanding NVMe controller resources

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `16b98a1bb33bcdabf20fef96b7027094942564c0e02da9a882240496a2594fca`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `16b98a1bb33bcdabf20fef96b7027094942564c0e02da9a882240496a2594fca`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `16b98a1bb33bcdabf20fef96b7027094942564c0e02da9a882240496a2594fca`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/drivers/nvme/nvme_freestanding_controller_spec.spl
mirror: doc/06_spec/unit/os/drivers/nvme/nvme_freestanding_controller_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/drivers/nvme/nvme_freestanding_controller_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/drivers/nvme/nvme_freestanding_controller_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/drivers/nvme/nvme_freestanding_controller_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'only reports ready after actual completion and reversible sector probes are supplied' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/drivers/nvme/nvme_freestanding_controller_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects probe evidence that bypasses shared transfer logic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/drivers/nvme/nvme_freestanding_controller_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects invalid controller resources before transfer evidence can be built' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
