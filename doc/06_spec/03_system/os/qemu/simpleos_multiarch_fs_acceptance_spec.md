# Multi-architecture filesystem execution acceptance

> Validates the common x86_64, ARM64, and RV64 QEMU/native lifecycle contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multi-architecture filesystem execution acceptance

Validates the common x86_64, ARM64, and RV64 QEMU/native lifecycle contract.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/simpleos_multiarch_fs_acceptance_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Validates the common x86_64, ARM64, and RV64 QEMU/native lifecycle contract.
Rows fail closed unless filesystem lookup, authenticated adoption, exit 37,
exact reap, address-space/handle reclamation, and canonical native performance
receipts are all present.

## Scenarios

### REQ-008: QEMU filesystem launch adoption and reclamation

#### accepts the same complete lifecycle on x86_64 ARM64 and RV64

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-008
```

</details>

#### fails closed when launch evidence or resource reclamation is absent

- fails closed when launch evidence or resource reclamation is absent


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fails closed when launch evidence or resource reclamation is absent")
var missing = candidate("arm64", SimpleOsEvidenceEnvironment.QemuSystem)
var receipt = missing.lifecycle
receipt.steps = receipt.steps.slice(0, 10)
missing.lifecycle = receipt
expect(simpleos_multiarch_fs_acceptance_validate(missing).error).to_equal(
    SimpleOsMultiarchFsAcceptanceErrorV1.MissingLifecycleStep)
var leaked = candidate("riscv64", SimpleOsEvidenceEnvironment.QemuSystem)
var after = leaked.after
after.mappings = after.mappings + 1u64
leaked.after = after
expect(simpleos_multiarch_fs_acceptance_validate(leaked).error).to_equal(
    SimpleOsMultiarchFsAcceptanceErrorV1.ResourceLeak)
```

</details>

#### rejects wrong exit status double reap and QEMU timing promotion

- rejects wrong exit status double reap and QEMU timing promotion


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects wrong exit status double reap and QEMU timing promotion")
var wrong_exit = candidate("x86_64", SimpleOsEvidenceEnvironment.QemuSystem)
wrong_exit.child_exit_code = 0
expect(simpleos_multiarch_fs_acceptance_validate(wrong_exit).error).to_equal(
    SimpleOsMultiarchFsAcceptanceErrorV1.ReapMismatch)
var double_reap = candidate("x86_64", SimpleOsEvidenceEnvironment.QemuSystem)
double_reap.reap_count = 2u64
expect(simpleos_multiarch_fs_acceptance_validate(double_reap).error).to_equal(
    SimpleOsMultiarchFsAcceptanceErrorV1.ReapMismatch)
var qemu_timing = candidate("x86_64", SimpleOsEvidenceEnvironment.QemuSystem)
qemu_timing.performance = [performance(SimpleOsPerformanceWorkloadV1.FsMetadata, 1000u64)]
expect(simpleos_multiarch_fs_acceptance_validate(qemu_timing).error).to_equal(
    SimpleOsMultiarchFsAcceptanceErrorV1.PerformanceForbidden)
```

</details>

### NFR-002/003: native filesystem performance receipts

#### accepts native rows only with all canonical filesystem execution workloads

- accepts native rows only with all canonical filesystem execution workloads
- Validate raw native timing and RSS samples through the canonical performance owner


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accepts native rows only with all canonical filesystem execution workloads")
step("Validate raw native timing and RSS samples through the canonical performance owner")
for architecture in ["x86_64", "arm64", "riscv64"]:
    var native = candidate(architecture, SimpleOsEvidenceEnvironment.NativeHost)
    native.performance = [
        performance(SimpleOsPerformanceWorkloadV1.FsMetadata, 1000u64),
        performance(SimpleOsPerformanceWorkloadV1.FsSequentialThroughput, 120000000u64),
        performance(SimpleOsPerformanceWorkloadV1.SimpleCompileRun, 1000000u64)]
    expect(simpleos_multiarch_fs_acceptance_validate(native).ok).to_be(true)
```

</details>

#### fails closed on absent noisy short nonnative or incomplete receipts

- fails closed on absent noisy short nonnative or incomplete receipts


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fails closed on absent noisy short nonnative or incomplete receipts")
var absent = candidate("arm64", SimpleOsEvidenceEnvironment.NativeHost)
expect(simpleos_multiarch_fs_acceptance_validate(absent).error).to_equal(
    SimpleOsMultiarchFsAcceptanceErrorV1.MissingPerformanceWorkload)
var incomplete = candidate("riscv64", SimpleOsEvidenceEnvironment.NativeHost)
incomplete.performance = [
    performance(SimpleOsPerformanceWorkloadV1.FsMetadata, 1000u64),
    performance(SimpleOsPerformanceWorkloadV1.FsSequentialThroughput, 120000000u64)]
expect(simpleos_multiarch_fs_acceptance_validate(incomplete).error).to_equal(
    SimpleOsMultiarchFsAcceptanceErrorV1.MissingPerformanceWorkload)
var short = candidate("x86_64", SimpleOsEvidenceEnvironment.NativeHost)
var invalid = performance(SimpleOsPerformanceWorkloadV1.FsMetadata, 1000u64)
invalid.samples = [1000u64]
invalid.rss_samples = [100000u64]
short.performance = [invalid]
expect(simpleos_multiarch_fs_acceptance_validate(short).error).to_equal(
    SimpleOsMultiarchFsAcceptanceErrorV1.InvalidPerformanceEvidence)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-008`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4a5c895af379294c9ad7a9d88a2100706f7fe8d5a297c3ee4f054c6ee6fbb263`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4a5c895af379294c9ad7a9d88a2100706f7fe8d5a297c3ee4f054c6ee6fbb263`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4a5c895af379294c9ad7a9d88a2100706f7fe8d5a297c3ee4f054c6ee6fbb263`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/03_system/os/qemu/simpleos_multiarch_fs_acceptance_spec.spl
mirror: doc/06_spec/03_system/os/qemu/simpleos_multiarch_fs_acceptance_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/qemu/simpleos_multiarch_fs_acceptance_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/qemu/simpleos_multiarch_fs_acceptance_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/qemu/simpleos_multiarch_fs_acceptance_spec.spl:111:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'accepts the same complete lifecycle on x86_64 ARM64 and RV64' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/os/qemu/simpleos_multiarch_fs_acceptance_spec.spl:121:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed when launch evidence or resource reclamation is absent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/simpleos_multiarch_fs_acceptance_spec.spl:137:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects wrong exit status double reap and QEMU timing promotion' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/simpleos_multiarch_fs_acceptance_spec.spl:154:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts native rows only with all canonical filesystem execution workloads' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
