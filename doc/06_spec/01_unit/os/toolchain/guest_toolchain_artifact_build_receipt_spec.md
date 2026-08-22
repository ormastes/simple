# guest_toolchain_artifact_build_receipt_spec

> Verifies the guest toolchain artifact build receipt behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# guest_toolchain_artifact_build_receipt_spec

Verifies the guest toolchain artifact build receipt behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/toolchain/guest_toolchain_artifact_build_receipt_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the guest toolchain artifact build receipt behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### GuestToolchainArtifactBuildReceiptV1

#### admits reproducible target-matched ELF candidates for all required architectures

- Verify: admits reproducible target-matched ELF candidates for all required architectures
   - Expected: _admit(receipt, output, output) equals `Ok(())`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-010
# @req: REQ-009
step("Verify: admits reproducible target-matched ELF candidates for all required architectures")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: admits canonical SMF only for a Simple role and matching target
   - Expected: _admit(receipt, output, output) equals `Ok(())`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-010
# @req: REQ-009
step("Verify: admits canonical SMF only for a Simple role and matching target")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: rejects all-zero and malformed artifact placeholders


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-010
# @req: REQ-009
step("Verify: rejects all-zero and malformed artifact placeholders")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: rejects unknown and wrong-machine target rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-010
# @req: REQ-009
step("Verify: rejects unknown and wrong-machine target rows")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: rejects target ABI substitution independently of ELF machine


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-010
# @req: REQ-009
step("Verify: rejects target ABI substitution independently of ELF machine")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: requires an explicit non-seed builder and exact target/output argv bindings


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-010
# @req: REQ-009
step("Verify: requires an explicit non-seed builder and exact target/output argv bindings")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: rejects PATH lookup and host fallback independently


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-010
# @req: REQ-009
step("Verify: rejects PATH lookup and host fallback independently")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: re-hashes builder, source, provenance, and canonical argv


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-010
# @req: REQ-009
step("Verify: re-hashes builder, source, provenance, and canonical argv")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: re-hashes source revision, dependency manifest, and build environment material


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-010
# @req: REQ-009
step("Verify: re-hashes source revision, dependency manifest, and build environment material")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: requires a target-isolated output path and byte-identical rebuild


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-010
# @req: REQ-009
step("Verify: requires a target-isolated output path and byte-identical rebuild")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: rejects duplicate option bindings and frozen receipt mutation


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-010
# @req: REQ-009
step("Verify: rejects duplicate option bindings and frozen receipt mutation")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0e3a4224c6f6a2281fa399ca3f835776d4c37ac8aaca16b978647d9d984e7657`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0e3a4224c6f6a2281fa399ca3f835776d4c37ac8aaca16b978647d9d984e7657`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0e3a4224c6f6a2281fa399ca3f835776d4c37ac8aaca16b978647d9d984e7657`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/toolchain/guest_toolchain_artifact_build_receipt_spec.spl
mirror: doc/06_spec/01_unit/os/toolchain/guest_toolchain_artifact_build_receipt_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/toolchain/guest_toolchain_artifact_build_receipt_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/toolchain/guest_toolchain_artifact_build_receipt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/toolchain/guest_toolchain_artifact_build_receipt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
