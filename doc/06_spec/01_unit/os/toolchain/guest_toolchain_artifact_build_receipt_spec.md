# Guest Toolchain Artifact Build Receipt Specification

> Tests covering GuestToolchainArtifactBuildReceiptV1.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Guest Toolchain Artifact Build Receipt Specification

## Scenarios

### GuestToolchainArtifactBuildReceiptV1

#### admits reproducible target-matched ELF candidates for all required architectures

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- admits reproducible target-matched ELF candidates for all required architectures
   - Expected: _admit(receipt, output, output) equals `Ok(())`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("admits reproducible target-matched ELF candidates for all required architectures")
val targets = [
    "x86_64-unknown-simpleos",
    "aarch64-unknown-simpleos",
    "riscv64gc-unknown-simpleos"
]
for target in targets:
    val output = _elf64_candidate(_machine_for_target(target))
    val receipt = _receipt(
        target, GuestToolchainArtifactRoleV1.Clang,
        GuestToolchainArtifactFormatV1.Elf, output)
    expect(_admit(receipt, output, output)).to_equal(Ok(()))
```

</details>

#### admits canonical SMF only for a Simple role and matching target

- admits canonical SMF only for a Simple role and matching target
   - Expected: _admit(receipt, output, output) equals `Ok(())`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("admits canonical SMF only for a Simple role and matching target")
val target = "x86_64-unknown-simpleos"
val output = _smf_candidate(target)
val receipt = _receipt(
    target, GuestToolchainArtifactRoleV1.SimpleCompiler,
    GuestToolchainArtifactFormatV1.Smf, output)
expect(_admit(receipt, output, output)).to_equal(Ok(()))

var wrong_role = receipt
wrong_role.role = GuestToolchainArtifactRoleV1.Clang
expect(_admit(wrong_role, output, output).unwrap_err()).to_equal(
    GuestToolchainArtifactBuildAdmissionErrorV1.InvalidRoleFormat)
```

</details>

#### rejects all-zero and malformed artifact placeholders

- rejects all-zero and malformed artifact placeholders


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects all-zero and malformed artifact placeholders")
val zero = [0u8, 0u8, 0u8, 0u8]
val zero_receipt = _receipt(
    "x86_64-unknown-simpleos", GuestToolchainArtifactRoleV1.Clang,
    GuestToolchainArtifactFormatV1.Elf, zero)
expect(_admit(zero_receipt, zero, zero).unwrap_err()).to_equal(
    GuestToolchainArtifactBuildAdmissionErrorV1.OutputDigestMismatch)

val malformed = [1u8, 2u8, 3u8, 4u8]
val malformed_receipt = _receipt(
    "x86_64-unknown-simpleos", GuestToolchainArtifactRoleV1.Clang,
    GuestToolchainArtifactFormatV1.Elf, malformed)
expect(_admit(malformed_receipt, malformed, malformed).unwrap_err()).to_equal(
    GuestToolchainArtifactBuildAdmissionErrorV1.InvalidElfStructure)
```

</details>

#### rejects unknown and wrong-machine target rows

- rejects unknown and wrong-machine target rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects unknown and wrong-machine target rows")
val output = _elf64_candidate(62)
var receipt = _receipt(
    "x86_64-unknown-simpleos", GuestToolchainArtifactRoleV1.Clang,
    GuestToolchainArtifactFormatV1.Elf, output)
receipt.target_triple = "x86_64-unknown-linux-gnu"
expect(_admit(receipt, output, output).unwrap_err()).to_equal(
    GuestToolchainArtifactBuildAdmissionErrorV1.InvalidTarget)

receipt = _receipt(
    "aarch64-unknown-simpleos", GuestToolchainArtifactRoleV1.Clang,
    GuestToolchainArtifactFormatV1.Elf, output)
expect(_admit(receipt, output, output).unwrap_err()).to_equal(
    GuestToolchainArtifactBuildAdmissionErrorV1.InvalidElfStructure)
```

</details>

#### rejects target ABI substitution independently of ELF machine

- rejects target ABI substitution independently of ELF machine


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects target ABI substitution independently of ELF machine")
val output = _elf64_candidate(62)
var receipt = _receipt(
    "x86_64-unknown-simpleos", GuestToolchainArtifactRoleV1.Clang,
    GuestToolchainArtifactFormatV1.Elf, output)
receipt.target_abi = "gnu"
expect(_admit(receipt, output, output).unwrap_err()).to_equal(
    GuestToolchainArtifactBuildAdmissionErrorV1.InvalidAbi)
```

</details>

#### requires an explicit non-seed builder and exact target/output argv bindings

- requires an explicit non-seed builder and exact target/output argv bindings


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("requires an explicit non-seed builder and exact target/output argv bindings")
val output = _elf64_candidate(62)
var receipt = _receipt(
    "x86_64-unknown-simpleos", GuestToolchainArtifactRoleV1.Clang,
    GuestToolchainArtifactFormatV1.Elf, output)
receipt.builder_path = "simple"
expect(_admit(receipt, output, output).unwrap_err()).to_equal(
    GuestToolchainArtifactBuildAdmissionErrorV1.InvalidBuilderPath)

receipt = _receipt(
    "x86_64-unknown-simpleos", GuestToolchainArtifactRoleV1.Clang,
    GuestToolchainArtifactFormatV1.Elf, output)
receipt.builder_path = "src/compiler_rust/target/bootstrap/simple"
expect(_admit(receipt, output, output).unwrap_err()).to_equal(
    GuestToolchainArtifactBuildAdmissionErrorV1.ForbiddenBootstrapBuilder)

receipt = _receipt(
    "x86_64-unknown-simpleos", GuestToolchainArtifactRoleV1.Clang,
    GuestToolchainArtifactFormatV1.Elf, output)
receipt.builder_argv = [receipt.builder_path, "--target", receipt.target_triple]
receipt.build_command_sha256 = guest_toolchain_artifact_build_command_sha256_v1(receipt.builder_argv)
expect(_admit(receipt, output, output).unwrap_err()).to_equal(
    GuestToolchainArtifactBuildAdmissionErrorV1.InvalidArgv)
```

</details>

#### rejects PATH lookup and host fallback independently

- rejects PATH lookup and host fallback independently


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects PATH lookup and host fallback independently")
val output = _elf64_candidate(62)
var receipt = _receipt(
    "x86_64-unknown-simpleos", GuestToolchainArtifactRoleV1.Clang,
    GuestToolchainArtifactFormatV1.Elf, output)
receipt.used_path_lookup = true
expect(_admit(receipt, output, output).unwrap_err()).to_equal(
    GuestToolchainArtifactBuildAdmissionErrorV1.PathLookupForbidden)

receipt = _receipt(
    "x86_64-unknown-simpleos", GuestToolchainArtifactRoleV1.Clang,
    GuestToolchainArtifactFormatV1.Elf, output)
receipt.used_host_fallback = true
expect(_admit(receipt, output, output).unwrap_err()).to_equal(
    GuestToolchainArtifactBuildAdmissionErrorV1.HostFallbackForbidden)
```

</details>

#### re-hashes builder, source, provenance, and canonical argv

- re-hashes builder, source, provenance, and canonical argv


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("re-hashes builder, source, provenance, and canonical argv")
val output = _elf64_candidate(62)
var receipt = _receipt(
    "x86_64-unknown-simpleos", GuestToolchainArtifactRoleV1.Clang,
    GuestToolchainArtifactFormatV1.Elf, output)
receipt.builder_sha256 = sha256_u8_hex([0x99u8])
expect(_admit(receipt, output, output).unwrap_err()).to_equal(
    GuestToolchainArtifactBuildAdmissionErrorV1.BuilderDigestMismatch)

receipt = _receipt(
    "x86_64-unknown-simpleos", GuestToolchainArtifactRoleV1.Clang,
    GuestToolchainArtifactFormatV1.Elf, output)
receipt.builder_source_sha256 = sha256_u8_hex([0x99u8])
expect(_admit(receipt, output, output).unwrap_err()).to_equal(
    GuestToolchainArtifactBuildAdmissionErrorV1.BuilderSourceDigestMismatch)

receipt = _receipt(
    "x86_64-unknown-simpleos", GuestToolchainArtifactRoleV1.Clang,
    GuestToolchainArtifactFormatV1.Elf, output)
receipt.builder_provenance_sha256 = sha256_u8_hex([0x99u8])
expect(_admit(receipt, output, output).unwrap_err()).to_equal(
    GuestToolchainArtifactBuildAdmissionErrorV1.ProvenanceDigestMismatch)

receipt = _receipt(
    "x86_64-unknown-simpleos", GuestToolchainArtifactRoleV1.Clang,
    GuestToolchainArtifactFormatV1.Elf, output)
receipt.build_command_sha256 = sha256_u8_hex([0x99u8])
expect(_admit(receipt, output, output).unwrap_err()).to_equal(
    GuestToolchainArtifactBuildAdmissionErrorV1.BuildCommandDigestMismatch)
```

</details>

#### re-hashes source revision, dependency manifest, and build environment material

- re-hashes source revision, dependency manifest, and build environment material


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("re-hashes source revision, dependency manifest, and build environment material")
val output = _elf64_candidate(62)
val receipt = _receipt(
    "x86_64-unknown-simpleos", GuestToolchainArtifactRoleV1.Clang,
    GuestToolchainArtifactFormatV1.Elf, output)
expect(_admit_materials(
    receipt, [0x99u8], _dependency_manifest_bytes(),
    _build_environment_bytes(), output, output).unwrap_err()).to_equal(
    GuestToolchainArtifactBuildAdmissionErrorV1.SourceRevisionDigestMismatch)

expect(_admit_materials(
    receipt, _source_revision_bytes(), [0x99u8],
    _build_environment_bytes(), output, output).unwrap_err()).to_equal(
    GuestToolchainArtifactBuildAdmissionErrorV1.DependencyManifestDigestMismatch)

expect(_admit_materials(
    receipt, _source_revision_bytes(), _dependency_manifest_bytes(),
    [0x99u8], output, output).unwrap_err()).to_equal(
    GuestToolchainArtifactBuildAdmissionErrorV1.BuildEnvironmentDigestMismatch)

expect(_admit_materials(
    receipt, [], _dependency_manifest_bytes(),
    _build_environment_bytes(), output, output).unwrap_err()).to_equal(
    GuestToolchainArtifactBuildAdmissionErrorV1.InvalidProvenanceMaterial)
```

</details>

#### requires a target-isolated output path and byte-identical rebuild

- requires a target-isolated output path and byte-identical rebuild


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("requires a target-isolated output path and byte-identical rebuild")
val output = _elf64_candidate(62)
var receipt = _receipt(
    "x86_64-unknown-simpleos", GuestToolchainArtifactRoleV1.Clang,
    GuestToolchainArtifactFormatV1.Elf, output)
receipt.output_path = "build/os/clang_static/bin/clang_static"
expect(_admit(receipt, output, output).unwrap_err()).to_equal(
    GuestToolchainArtifactBuildAdmissionErrorV1.InvalidOutputPath)

receipt = _receipt(
    "x86_64-unknown-simpleos", GuestToolchainArtifactRoleV1.Clang,
    GuestToolchainArtifactFormatV1.Elf, output)
var different = output
different[120] = 0x90u8
expect(_admit(receipt, output, different).unwrap_err()).to_equal(
    GuestToolchainArtifactBuildAdmissionErrorV1.RebuildDigestMismatch)

receipt = _receipt(
    "x86_64-unknown-simpleos", GuestToolchainArtifactRoleV1.Clang,
    GuestToolchainArtifactFormatV1.Elf, output)
receipt.output_size = output.len() + 1
expect(_admit(receipt, output, output).unwrap_err()).to_equal(
    GuestToolchainArtifactBuildAdmissionErrorV1.InvalidOutputSize)
```

</details>

#### rejects duplicate option bindings and frozen receipt mutation

- rejects duplicate option bindings and frozen receipt mutation


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects duplicate option bindings and frozen receipt mutation")
val output = _elf64_candidate(62)
var receipt = _receipt(
    "x86_64-unknown-simpleos", GuestToolchainArtifactRoleV1.Clang,
    GuestToolchainArtifactFormatV1.Elf, output)
receipt.builder_argv = receipt.builder_argv + [
    "--target", receipt.target_triple, "--output", receipt.output_path]
receipt.build_command_sha256 =
    guest_toolchain_artifact_build_command_sha256_v1(receipt.builder_argv)
expect(_admit(receipt, output, output).unwrap_err()).to_equal(
    GuestToolchainArtifactBuildAdmissionErrorV1.InvalidArgv)

receipt = _receipt(
    "x86_64-unknown-simpleos", GuestToolchainArtifactRoleV1.Clang,
    GuestToolchainArtifactFormatV1.Elf, output)
receipt.receipt_id = "toolchain-artifact-build-forged"
expect(_admit(receipt, output, output).unwrap_err()).to_equal(
    GuestToolchainArtifactBuildAdmissionErrorV1.ReceiptPayloadDigestMismatch)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/toolchain/guest_toolchain_artifact_build_receipt_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering GuestToolchainArtifactBuildReceiptV1.
- GuestToolchainArtifactBuildReceiptV1

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `e3f2c67e39c3b8c2f35d6f55d2665cf904297794ef4d8b65408de15465a777cd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e3f2c67e39c3b8c2f35d6f55d2665cf904297794ef4d8b65408de15465a777cd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e3f2c67e39c3b8c2f35d6f55d2665cf904297794ef4d8b65408de15465a777cd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/toolchain/guest_toolchain_artifact_build_receipt_spec.spl
mirror: doc/06_spec/01_unit/os/toolchain/guest_toolchain_artifact_build_receipt_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/os/toolchain/guest_toolchain_artifact_build_receipt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/toolchain/guest_toolchain_artifact_build_receipt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/toolchain/guest_toolchain_artifact_build_receipt_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/toolchain/guest_toolchain_artifact_build_receipt_spec.spl:175:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits reproducible target-matched ELF candidates for all required architectures' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/toolchain/guest_toolchain_artifact_build_receipt_spec.spl:190:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits canonical SMF only for a Simple role and matching target' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/toolchain/guest_toolchain_artifact_build_receipt_spec.spl:205:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects all-zero and malformed artifact placeholders' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
