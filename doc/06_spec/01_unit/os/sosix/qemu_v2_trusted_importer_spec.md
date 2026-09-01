# Qemu V2 Trusted Importer Specification

> Tests covering SOSIX QEMU v2 trusted importer.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Qemu V2 Trusted Importer Specification

## Scenarios

### SOSIX QEMU v2 trusted importer

#### accepts a complete byte-bound 24-cell direct-kernel collector root

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts a complete byte-bound 24-cell direct-kernel collector root


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a complete byte-bound 24-cell direct-kernel collector root")
val root = _qemu_v2_setup_full_matrix(_QEMU_V2_FIXTURE_ROOT, false)
expect(sosix_qemu_collector_root_is_release_admissible(root)).to_be(true)
```

</details>

#### rejects exact admission-record byte mutation after manifest publication

- rejects exact admission-record byte mutation after manifest publication


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects exact admission-record byte mutation after manifest publication")
val root = _qemu_v2_setup_full_matrix(_QEMU_V2_FIXTURE_ROOT, false)
expect(sosix_qemu_collector_root_is_release_admissible(root)).to_be(true)
val mutated = _qemu_v2_admission(
    "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
    _qemu_v2_write_artifacts(root, "linux", "x86_32"))
expect(file_write_text(root + "/rows/linux/x86_32/admission.env", mutated)).to_be(true)
expect(sosix_qemu_collector_root_is_release_admissible(root)).to_be(false)
```

</details>

#### rejects a malformed final row after twenty-three valid rows

- rejects a malformed final row after twenty-three valid rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a malformed final row after twenty-three valid rows")
val root = _qemu_v2_setup_full_matrix(_QEMU_V2_FIXTURE_ROOT, true)
expect(sosix_qemu_collector_root_is_release_admissible(root)).to_be(false)
```

</details>

#### rejects a complete but noncanonical collector row permutation

- rejects a complete but noncanonical collector row permutation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a complete but noncanonical collector row permutation")
val root = _qemu_v2_setup_full_matrix(
    _QEMU_V2_FIXTURE_ROOT, false, swap_first_two_rows: true)
expect(sosix_qemu_collector_root_is_release_admissible(root)).to_be(false)
```

</details>

#### rejects a retained artifact changed after evidence publication

- rejects a retained artifact changed after evidence publication


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a retained artifact changed after evidence publication")
val root = _qemu_v2_setup_full_matrix(_QEMU_V2_FIXTURE_ROOT, false)
val artifact = root + "/rows/freebsd/riscv64/artifacts/program.elf"
expect(file_write_text(artifact, "late artifact mutation\n")).to_be(true)
expect(sosix_qemu_collector_root_is_release_admissible(root)).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/sosix/qemu_v2_trusted_importer_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SOSIX QEMU v2 trusted importer.
- SOSIX QEMU v2 trusted importer

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0d0ab7eb2fd6803666941e863e9e887036a9ccb0d7c9a7ec18c52820c7ecbeed`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0d0ab7eb2fd6803666941e863e9e887036a9ccb0d7c9a7ec18c52820c7ecbeed`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0d0ab7eb2fd6803666941e863e9e887036a9ccb0d7c9a7ec18c52820c7ecbeed`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/sosix/qemu_v2_trusted_importer_spec.spl
mirror: doc/06_spec/01_unit/os/sosix/qemu_v2_trusted_importer_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/sosix/qemu_v2_trusted_importer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/sosix/qemu_v2_trusted_importer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/sosix/qemu_v2_trusted_importer_spec.spl:183:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a complete byte-bound 24-cell direct-kernel collector root' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/sosix/qemu_v2_trusted_importer_spec.spl:189:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects exact admission-record byte mutation after manifest publication' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/sosix/qemu_v2_trusted_importer_spec.spl:200:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a malformed final row after twenty-three valid rows' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
