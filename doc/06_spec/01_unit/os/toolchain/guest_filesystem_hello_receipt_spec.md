# Guest Filesystem Hello Receipt Specification

> Tests covering Guest filesystem hello-world receipt v1.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Guest Filesystem Hello Receipt Specification

## Scenarios

### Guest filesystem hello-world receipt v1

#### projects byte-backed candidates on every target and filesystem

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- projects byte-backed candidates on every target and filesystem


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("projects byte-backed candidates on every target and filesystem")
val targets = [
    "x86_64-unknown-simpleos", "aarch64-unknown-simpleos",
    "riscv64gc-unknown-simpleos"
]
val filesystems = [
    GuestToolchainFilesystem.Fat32,
    GuestToolchainFilesystem.Dbfs,
    GuestToolchainFilesystem.Nvfs
]
val source = "#include <stdio.h>\nint main(void){puts(\"Hello World\");}\n".bytes()
val object = [1u8, 2u8, 3u8]
for target in targets:
    val executable = _elf(target)
    for filesystem in filesystems:
        val receipt = _receipt(target, filesystem, source, object, executable)
        expect(guest_filesystem_hello_candidate_project_v1(
            receipt, executable, executable, source, object,
            executable)).to_equal(Ok(
            GuestFilesystemHelloProjectionV1.StructurallyConsistentNonAuthorizing))
```

</details>

#### fails closed when any target artifact is absent

- fails closed when any target artifact is absent


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("fails closed when any target artifact is absent")
val source = "int main(void){return 0;}\n".bytes()
val object = [1u8]
val executable = _elf("x86_64-unknown-simpleos")
val receipt = _receipt(
    "x86_64-unknown-simpleos", GuestToolchainFilesystem.Fat32,
    source, object, executable)
expect(guest_filesystem_hello_candidate_project_v1(
    receipt, executable, executable, source, [],
    executable).unwrap_err()).to_equal(
    GuestFilesystemHelloAdmissionErrorV1.MissingArtifact)
```

</details>

#### rejects host execution, PATH lookup, filesystem substitution, and output claims

- rejects host execution, PATH lookup, filesystem substitution, and output claims


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects host execution, PATH lookup, filesystem substitution, and output claims")
val source = "int main(void){return 0;}\n".bytes()
val object = [1u8]
val executable = _elf("x86_64-unknown-simpleos")
var receipt = _receipt(
    "x86_64-unknown-simpleos", GuestToolchainFilesystem.Fat32,
    source, object, executable)
receipt.used_host_process = true
expect(guest_filesystem_hello_candidate_project_v1(
    receipt, executable, executable, source, object,
    executable).unwrap_err()).to_equal(
    GuestFilesystemHelloAdmissionErrorV1.HostExecutionForbidden)

receipt.used_host_process = false
receipt.used_path_lookup = true
expect(guest_filesystem_hello_candidate_project_v1(
    receipt, executable, executable, source, object,
    executable).unwrap_err()).to_equal(
    GuestFilesystemHelloAdmissionErrorV1.PathLookupForbidden)

receipt.used_path_lookup = false
receipt.filesystem = GuestToolchainFilesystem.Dbfs
expect(guest_filesystem_hello_candidate_project_v1(
    receipt, executable, executable, source, object,
    executable).unwrap_err()).to_equal(
    GuestFilesystemHelloAdmissionErrorV1.InvalidFilesystem)

receipt.filesystem = GuestToolchainFilesystem.Fat32
receipt.observed_stdout = ""
expect(guest_filesystem_hello_candidate_project_v1(
    receipt, executable, executable, source, object,
    executable).unwrap_err()).to_equal(
    GuestFilesystemHelloAdmissionErrorV1.OutputMismatch)
```

</details>

#### never authorizes a forged caller-asserted in-guest candidate

- never authorizes a forged caller-asserted in-guest candidate


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("never authorizes a forged caller-asserted in-guest candidate")
val source = "int main(void){return 0;}\n".bytes()
val object = [1u8]
val executable = _elf("x86_64-unknown-simpleos")
# Every execution boolean and transcript below is caller-controlled.
# Structural consistency must remain non-authorizing even when forged.
val forged = _receipt(
    "x86_64-unknown-simpleos", GuestToolchainFilesystem.Fat32,
    source, object, executable)
val projection = guest_filesystem_hello_candidate_project_v1(
    forged, executable, executable, source, object, executable).unwrap()
expect(projection).to_equal(
    GuestFilesystemHelloProjectionV1.StructurallyConsistentNonAuthorizing)
expect(guest_filesystem_hello_projection_authorizes_guest_execution_v1(
    projection)).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/toolchain/guest_filesystem_hello_receipt_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Guest filesystem hello-world receipt v1.
- Guest filesystem hello-world receipt v1

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
- `REQ-009/010`
- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `88d653e710e4642c8e777ac3f010dbb1e173642a9e81eacf1c348f810af7396f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `88d653e710e4642c8e777ac3f010dbb1e173642a9e81eacf1c348f810af7396f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `88d653e710e4642c8e777ac3f010dbb1e173642a9e81eacf1c348f810af7396f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/toolchain/guest_filesystem_hello_receipt_spec.spl
mirror: doc/06_spec/01_unit/os/toolchain/guest_filesystem_hello_receipt_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/os/toolchain/guest_filesystem_hello_receipt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/toolchain/guest_filesystem_hello_receipt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/toolchain/guest_filesystem_hello_receipt_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/toolchain/guest_filesystem_hello_receipt_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'projects byte-backed candidates on every target and filesystem' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/toolchain/guest_filesystem_hello_receipt_spec.spl:129:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed when any target artifact is absent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/toolchain/guest_filesystem_hello_receipt_spec.spl:143:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects host execution, PATH lookup, filesystem substitution, and output claims' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
