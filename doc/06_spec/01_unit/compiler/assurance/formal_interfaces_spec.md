# Formal Interfaces Specification

> Tests covering Formal Verification 2.0 frozen interfaces.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Formal Interfaces Specification

## Scenarios

### Formal Verification 2.0 frozen interfaces

#### makes advice order part of the weave identity

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- makes advice order part of the weave identity
   - Expected: first.diagnostic() equals ``
   - Expected: first.hash() == second.hash() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("makes advice order part of the weave identity")
val first = WeaveManifestV1("base", "macro", [WeaveJoinPointV1("42", ["before", "around"])], [], "woven")
val second = WeaveManifestV1("base", "macro", [WeaveJoinPointV1("42", ["around", "before"])], [], "woven")
expect(first.diagnostic()).to_equal("")
expect(first.hash() == second.hash()).to_equal(false)
```

</details>

#### rejects unordered or duplicate join point identities

- rejects unordered or duplicate join point identities


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unordered or duplicate join point identities")
val manifest = WeaveManifestV1("base", "macro", [WeaveJoinPointV1("9", []), WeaveJoinPointV1("2", [])], [], "woven")
expect(manifest.diagnostic()).to_contain("ORDER")
```

</details>

#### requires independently checked compiler certificates

- requires independently checked compiler certificates


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires independently checked compiler certificates")
val unchecked = CompilerCertificateV1("lower", "before", "after", CompilerRefinementRelationV1.BehaviorInclusion, "validator-v1", "certificate", false)
expect(unchecked.diagnostic()).to_contain("CHECK")
```

</details>

#### rejects a forged compiler certificate hash

- rejects a forged compiler certificate hash


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a forged compiler certificate hash")
val forged = CompilerCertificateV1("lower", "before", "after", CompilerRefinementRelationV1.BehaviorInclusion, "validator-v1", "forged", true)
expect(forged.diagnostic()).to_contain("HASH")
```

</details>

#### requires bounded monitors and exactly-once behavior refinement

- requires bounded monitors and exactly-once behavior refinement


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires bounded monitors and exactly-once behavior refinement")
val monitor = AspectCertificateV1("monitor", AspectEvidenceClassV1.BoundedRuntimeMonitor, "base", "woven", "proof", false, false)
expect(monitor.diagnostic()).to_contain("BOUND")
val around = AspectCertificateV1("around", AspectEvidenceClassV1.BehaviorRefinement, "base", "woven", "proof", true, false)
expect(around.diagnostic()).to_contain("PROCEED")
```

</details>

#### binds a runtime monitor to one assumption VIR artifact and fail-stop policy

- binds a runtime monitor to one assumption VIR artifact and fail-stop policy
   - Expected: receipt.diagnostic() equals ``
   - Expected: receipt.hash() == "" is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("binds a runtime monitor to one assumption VIR artifact and fail-stop policy")
val receipt = RuntimeAssumptionMonitorReceiptV1("monitor",
    "timer_monotonic", sha256_text("vir"), sha256_text("artifact"),
    sha256_text("monitor-binary"), sha256_text("monitor-proof"),
    32, RuntimeMonitorFailStopV1.Trap)
expect(receipt.diagnostic()).to_equal("")
expect(receipt.hash() == "").to_equal(false)
val unbounded = RuntimeAssumptionMonitorReceiptV1("monitor",
    "timer_monotonic", sha256_text("vir"), sha256_text("artifact"),
    sha256_text("monitor-binary"), sha256_text("monitor-proof"),
    0, RuntimeMonitorFailStopV1.Trap)
expect(unbounded.diagnostic()).to_contain("BOUND")
```

</details>

#### does not verify hardware without cover mutation and netlist evidence

- does not verify hardware without cover mutation and netlist evidence
   - Expected: incomplete.permits_verified_release() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not verify hardware without cover mutation and netlist evidence")
val incomplete = HardwareProofReceiptV1("hwir", "rtl", "", "rvfi", ["rv32i-add"], [], [], ["sby"], ["job-receipt"], "trust", FormalStatus.ArtifactVerified)
expect(incomplete.permits_verified_release()).to_equal(false)
expect(incomplete.diagnostic()).to_contain("COVER")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/assurance/formal_interfaces_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Formal Verification 2.0 frozen interfaces.
- Formal Verification 2.0 frozen interfaces

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `05f4def35c1975b1cc6a7f1458f6fda33715e505ec16acde8b448cc1e2a54e4f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `05f4def35c1975b1cc6a7f1458f6fda33715e505ec16acde8b448cc1e2a54e4f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `05f4def35c1975b1cc6a7f1458f6fda33715e505ec16acde8b448cc1e2a54e4f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/assurance/formal_interfaces_spec.spl
mirror: doc/06_spec/01_unit/compiler/assurance/formal_interfaces_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/assurance/formal_interfaces_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/assurance/formal_interfaces_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/assurance/formal_interfaces_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'makes advice order part of the weave identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/assurance/formal_interfaces_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects unordered or duplicate join point identities' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/assurance/formal_interfaces_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires independently checked compiler certificates' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
