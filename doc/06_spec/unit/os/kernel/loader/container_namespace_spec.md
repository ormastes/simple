# Container Namespace Specification

> Tests covering SimpleOS container namespace contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Container Namespace Specification

## Scenarios

### SimpleOS container namespace contract

#### requires pid, filesystem, IPC, network, and capability evidence

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- requires pid, filesystem, IPC, network, and capability evidence
   - Expected: simpleos_container_namespace_gate(evidence) equals `missing-capability`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires pid, filesystem, IPC, network, and capability evidence")
val evidence = simpleos_container_namespace_evidence(42, "/containers/wine", true, true, true, false)
expect(evidence).to_contain("pid")
expect(evidence).to_contain("net")
expect(simpleos_container_namespace_gate(evidence)).to_equal("missing-capability")
```

</details>

#### keeps app paths resolved under the container rootfs

- keeps app paths resolved under the container rootfs
   - Expected: simpleos_container_rootfs_gate("/containers/wine", "/sys/apps/wine_hello") equals `ready`
   - Expected: simpleos_container_rootfs_gate("/", "/sys/apps/wine_hello") equals `invalid-rootfs`
   - Expected: simpleos_container_rootfs_gate("/containers/wine", "/etc/passwd") equals `invalid-app-path`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps app paths resolved under the container rootfs")
expect(simpleos_container_rootfs_gate("/containers/wine", "/sys/apps/wine_hello")).to_equal("ready")
expect(simpleos_container_rootfs_gate("/", "/sys/apps/wine_hello")).to_equal("invalid-rootfs")
expect(simpleos_container_rootfs_gate("/containers/wine", "/etc/passwd")).to_equal("invalid-app-path")
```

</details>

#### builds desktop serial markers for a Wine app container

- builds desktop serial markers for a Wine app container
   - Expected: contract.ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds desktop serial markers for a Wine app container")
val contract = simpleos_wine_container_contract(42, "/containers/wine", "/sys/apps/wine_hello", "nvfs")
expect(contract.ok).to_equal(true)
expect(contract.evidence).to_contain("capability")
expect(contract.namespace_marker).to_contain("[desktop-e2e] container-namespace:ok")
expect(contract.namespace_marker).to_contain("pid")
expect(contract.rootfs_marker).to_contain("[desktop-e2e] container-rootfs:ok")
expect(contract.rootfs_marker).to_contain("rootfs_backend=nvfs")
```

</details>

#### does not produce ok markers for invalid rootfs contracts

- does not produce ok markers for invalid rootfs contracts
   - Expected: contract.ok is false
   - Expected: contract.error equals `invalid-rootfs`
   - Expected: contract.namespace_marker equals ``
   - Expected: contract.rootfs_marker equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not produce ok markers for invalid rootfs contracts")
val contract = simpleos_wine_container_contract(42, "/", "/sys/apps/wine_hello", "nvfs")
expect(contract.ok).to_equal(false)
expect(contract.error).to_equal("invalid-rootfs")
expect(contract.namespace_marker).to_equal("")
expect(contract.rootfs_marker).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/kernel/loader/container_namespace_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS container namespace contract.
- SimpleOS container namespace contract

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

- Canonical SPipe generation for source `db385589de4b1691f73ae8c8501711fa2ef2e88f7b981c4df762a719497060a5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `db385589de4b1691f73ae8c8501711fa2ef2e88f7b981c4df762a719497060a5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `db385589de4b1691f73ae8c8501711fa2ef2e88f7b981c4df762a719497060a5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/kernel/loader/container_namespace_spec.spl
mirror: doc/06_spec/unit/os/kernel/loader/container_namespace_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/kernel/loader/container_namespace_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/loader/container_namespace_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/loader/container_namespace_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps app paths resolved under the container rootfs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/loader/container_namespace_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds desktop serial markers for a Wine app container' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/loader/container_namespace_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not produce ok markers for invalid rootfs contracts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
