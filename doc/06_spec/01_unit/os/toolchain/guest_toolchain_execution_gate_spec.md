# guest_toolchain_execution_gate_spec

> Verifies the guest toolchain execution gate behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# guest_toolchain_execution_gate_spec

Verifies the guest toolchain execution gate behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/toolchain/guest_toolchain_execution_gate_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the guest toolchain execution gate behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### target-native guest toolchain typed receipt

#### accepts structurally complete candidates for each required target and filesystem

- Verify: accepts structurally complete candidates for each required target and filesystem
   - Expected: guest_toolchain_execution_receipt_v1_validate(receipt) equals `Ok(())`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-010
# @req: REQ-009
step("Verify: accepts structurally complete candidates for each required target and filesystem")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val targets = [
    SIMPLEOS_TARGET_V1_X86_64_TRIPLE,
    SIMPLEOS_TARGET_V1_AARCH64_TRIPLE,
    SIMPLEOS_TARGET_V1_RISCV64GC_TRIPLE
]
val filesystems = [
    GuestToolchainFilesystem.Fat32,
    GuestToolchainFilesystem.Dbfs,
    GuestToolchainFilesystem.Nvfs
]
for target in targets:
    for filesystem in filesystems:
        val receipt = _receipt(target, filesystem)
        expect(guest_toolchain_execution_receipt_v1_validate(receipt)).to_equal(Ok(()))
        expect(guest_toolchain_execution_candidate_ready_for_evidence_admission(receipt)).to_be(true)
```

</details>

#### never promotes a structurally complete candidate directly to ledger PASS

- Verify: never promotes a structurally complete candidate directly to ledger PASS


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-010
# @req: REQ-009
step("Verify: never promotes a structurally complete candidate directly to ledger PASS")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val detail = guest_toolchain_execution_receipt_gate_detail(_x86_fat32_receipt())
expect(detail).to_start_with("BLOCKED:")
expect(detail).to_contain("authoritative producer signature")
expect(detail).to_contain("loader-owned consume-once token")
```

</details>

#### rejects wrong target, ABI, filesystem, and duplicate role substitution

- Verify: rejects wrong target, ABI, filesystem, and duplicate role substitution


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-010
# @req: REQ-009
step("Verify: rejects wrong target, ABI, filesystem, and duplicate role substitution")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var receipt = _x86_fat32_receipt()
receipt.target_triple = "x86_64-unknown-linux-gnu"
expect(guest_toolchain_execution_receipt_v1_validate(receipt).unwrap_err()).to_equal(
    GuestToolchainExecutionReceiptError.InvalidTarget)

receipt = _x86_fat32_receipt()
receipt.target_abi = "gnu"
expect(guest_toolchain_execution_receipt_v1_validate(receipt).unwrap_err()).to_equal(
    GuestToolchainExecutionReceiptError.InvalidAbi)

receipt = _x86_fat32_receipt()
var wrong_fs = receipt.roles[0]
wrong_fs.filesystem_source = GuestToolchainFilesystem.Dbfs
receipt.roles[0] = wrong_fs
expect(guest_toolchain_execution_receipt_v1_validate(receipt).unwrap_err()).to_equal(
    GuestToolchainExecutionReceiptError.WrongRoleFilesystem)

receipt = _x86_fat32_receipt()
receipt.roles[6] = receipt.roles[0]
expect(guest_toolchain_execution_receipt_v1_validate(receipt).unwrap_err()).to_equal(
    GuestToolchainExecutionReceiptError.DuplicateRole)
```

</details>

#### rejects schema, receipt identity, missing roles, and per-role target substitution

- Verify: rejects schema, receipt identity, missing roles, and per-role target substitution


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-010
# @req: REQ-009
step("Verify: rejects schema, receipt identity, missing roles, and per-role target substitution")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var receipt = _x86_fat32_receipt()
receipt.schema_version = 2
expect(guest_toolchain_execution_receipt_v1_validate(receipt).unwrap_err()).to_equal(
    GuestToolchainExecutionReceiptError.InvalidSchema)

receipt = _x86_fat32_receipt()
receipt.nonce = ""
expect(guest_toolchain_execution_receipt_v1_validate(receipt).unwrap_err()).to_equal(
    GuestToolchainExecutionReceiptError.InvalidReceiptIdentity)

receipt = _x86_fat32_receipt()
receipt.roles.pop()
expect(guest_toolchain_execution_receipt_v1_validate(receipt).unwrap_err()).to_equal(
    GuestToolchainExecutionReceiptError.MissingRole)

receipt = _x86_fat32_receipt()
var wrong_target = receipt.roles[0]
wrong_target.target_triple = SIMPLEOS_TARGET_V1_AARCH64_TRIPLE
receipt.roles[0] = wrong_target
expect(guest_toolchain_execution_receipt_v1_validate(receipt).unwrap_err()).to_equal(
    GuestToolchainExecutionReceiptError.WrongRoleTarget)
```

</details>

#### requires canonical guest artifacts and nonzero content digests

- Verify: requires canonical guest artifacts and nonzero content digests


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-010
# @req: REQ-009
step("Verify: requires canonical guest artifacts and nonzero content digests")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var receipt = _x86_fat32_receipt()
var role = receipt.roles[4]
role.tool_artifact_path = "/host/usr/bin/clang"
receipt.roles[4] = role
expect(guest_toolchain_execution_receipt_v1_validate(receipt).unwrap_err()).to_equal(
    GuestToolchainExecutionReceiptError.WrongRoleArtifactPath)

receipt = _x86_fat32_receipt()
role = receipt.roles[4]
role.tool_artifact_sha256 = "0000000000000000000000000000000000000000000000000000000000000000"
receipt.roles[4] = role
expect(guest_toolchain_execution_receipt_v1_validate(receipt).unwrap_err()).to_equal(
    GuestToolchainExecutionReceiptError.InvalidArtifactDigest)

receipt = _x86_fat32_receipt()
receipt.mount_receipt_sha256 = "not-a-sha256"
expect(guest_toolchain_execution_receipt_v1_validate(receipt).unwrap_err()).to_equal(
    GuestToolchainExecutionReceiptError.InvalidChainDigest)
```

</details>

#### requires absolute argv zero and binds the filesystem source into argv

- Verify: requires absolute argv zero and binds the filesystem source into argv


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-010
# @req: REQ-009
step("Verify: requires absolute argv zero and binds the filesystem source into argv")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var receipt = _x86_fat32_receipt()
var role = receipt.roles[3]
role.argv = ["llvm-ar", role.source_path]
receipt.roles[3] = role
expect(guest_toolchain_execution_receipt_v1_validate(receipt).unwrap_err()).to_equal(
    GuestToolchainExecutionReceiptError.InvalidArgv)

receipt = _x86_fat32_receipt()
role = receipt.roles[3]
role.source_path = "/work/../host-source"
receipt.roles[3] = role
expect(guest_toolchain_execution_receipt_v1_validate(receipt).unwrap_err()).to_equal(
    GuestToolchainExecutionReceiptError.InvalidSourcePath)

receipt = _x86_fat32_receipt()
role = receipt.roles[3]
role.source_sha256 = "uppercase-OR-short"
receipt.roles[3] = role
expect(guest_toolchain_execution_receipt_v1_validate(receipt).unwrap_err()).to_equal(
    GuestToolchainExecutionReceiptError.InvalidSourceDigest)

receipt = _x86_fat32_receipt()
role = receipt.roles[3]
role.working_directory = "relative/work"
receipt.roles[3] = role
expect(guest_toolchain_execution_receipt_v1_validate(receipt).unwrap_err()).to_equal(
    GuestToolchainExecutionReceiptError.InvalidWorkingDirectory)
```

</details>

#### rejects PATH lookup, host execution, and non-guest execution independently

- Verify: rejects PATH lookup, host execution, and non-guest execution independently


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-010
# @req: REQ-009
step("Verify: rejects PATH lookup, host execution, and non-guest execution independently")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var receipt = _x86_fat32_receipt()
var role = receipt.roles[0]
role.used_path_lookup = true
receipt.roles[0] = role
expect(guest_toolchain_execution_receipt_v1_validate(receipt).unwrap_err()).to_equal(
    GuestToolchainExecutionReceiptError.PathLookupForbidden)

receipt = _x86_fat32_receipt()
role = receipt.roles[0]
role.used_host_process = true
receipt.roles[0] = role
expect(guest_toolchain_execution_receipt_v1_validate(receipt).unwrap_err()).to_equal(
    GuestToolchainExecutionReceiptError.HostFallbackForbidden)

receipt = _x86_fat32_receipt()
role = receipt.roles[0]
role.executed_in_guest = false
receipt.roles[0] = role
expect(guest_toolchain_execution_receipt_v1_validate(receipt).unwrap_err()).to_equal(
    GuestToolchainExecutionReceiptError.GuestExecutionRequired)
```

</details>

#### requires exact bounded output, recomputed output digest, and exit zero

- Verify: requires exact bounded output, recomputed output digest, and exit zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-010
# @req: REQ-009
step("Verify: requires exact bounded output, recomputed output digest, and exit zero")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var receipt = _x86_fat32_receipt()
var role = receipt.roles[2]
role.observed_stdout = "host wrapper output\n"
receipt.roles[2] = role
expect(guest_toolchain_execution_receipt_v1_validate(receipt).unwrap_err()).to_equal(
    GuestToolchainExecutionReceiptError.OutputMismatch)

receipt = _x86_fat32_receipt()
role = receipt.roles[2]
role.observed_output_sha256 = sha256_text("forged-output")
receipt.roles[2] = role
expect(guest_toolchain_execution_receipt_v1_validate(receipt).unwrap_err()).to_equal(
    GuestToolchainExecutionReceiptError.OutputDigestMismatch)

receipt = _x86_fat32_receipt()
role = receipt.roles[2]
role.expected_exit_code = 1
role.observed_exit_code = 1
role.observed_output_sha256 = guest_toolchain_role_output_sha256(role)
receipt.roles[2] = role
expect(guest_toolchain_execution_receipt_v1_validate(receipt).unwrap_err()).to_equal(
    GuestToolchainExecutionReceiptError.ExitMismatch)

receipt = _x86_fat32_receipt()
role = receipt.roles[2]
role.expected_stdout = "x".repeat(65537)
role.observed_stdout = role.expected_stdout
receipt.roles[2] = role
expect(guest_toolchain_execution_receipt_v1_validate(receipt).unwrap_err()).to_equal(
    GuestToolchainExecutionReceiptError.OutputTooLarge)
```

</details>

#### binds every simple alias and the manifest to the distinct role digests

- Verify: binds every simple alias and the manifest to the distinct role digests


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-010
# @req: REQ-009
step("Verify: binds every simple alias and the manifest to the distinct role digests")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var receipt = _x86_fat32_receipt()
receipt.aliases.pop()
expect(guest_toolchain_execution_receipt_v1_validate(receipt).unwrap_err()).to_equal(
    GuestToolchainExecutionReceiptError.MissingAlias)

receipt = _x86_fat32_receipt()
receipt.aliases[5] = receipt.aliases[0]
expect(guest_toolchain_execution_receipt_v1_validate(receipt).unwrap_err()).to_equal(
    GuestToolchainExecutionReceiptError.DuplicateAlias)

receipt = _x86_fat32_receipt()
var alias_binding = receipt.aliases[0]
alias_binding.intended_role = GuestToolchainRole.SimpleInterpreter
receipt.aliases[0] = alias_binding
expect(guest_toolchain_execution_receipt_v1_validate(receipt).unwrap_err()).to_equal(
    GuestToolchainExecutionReceiptError.WrongAliasRole)

receipt = _x86_fat32_receipt()
alias_binding = receipt.aliases[0]
alias_binding.artifact_sha256 = sha256_text("different-artifact")
receipt.aliases[0] = alias_binding
expect(guest_toolchain_execution_receipt_v1_validate(receipt).unwrap_err()).to_equal(
    GuestToolchainExecutionReceiptError.AliasDigestMismatch)

receipt = _x86_fat32_receipt()
receipt.manifest_path = "/sys/simpletool.sdn"
expect(guest_toolchain_execution_receipt_v1_validate(receipt).unwrap_err()).to_equal(
    GuestToolchainExecutionReceiptError.InvalidManifestPath)

receipt = _x86_fat32_receipt()
receipt.manifest_loader_sha256 = receipt.manifest_compiler_sha256
expect(guest_toolchain_execution_receipt_v1_validate(receipt).unwrap_err()).to_equal(
    GuestToolchainExecutionReceiptError.ManifestRoleDigestMismatch)

receipt = _x86_fat32_receipt()
receipt.manifest_sha256 = sha256_text("forged-manifest-contract")
expect(guest_toolchain_execution_receipt_v1_validate(receipt).unwrap_err()).to_equal(
    GuestToolchainExecutionReceiptError.ManifestContractDigestMismatch)
```

</details>

#### requires canonical role and alias manifest ordering

- Verify: requires canonical role and alias manifest ordering


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-010
# @req: REQ-009
step("Verify: requires canonical role and alias manifest ordering")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var receipt = _x86_fat32_receipt()
val first_role = receipt.roles[0]
receipt.roles[0] = receipt.roles[1]
receipt.roles[1] = first_role
expect(guest_toolchain_execution_receipt_v1_validate(receipt).unwrap_err()).to_equal(
    GuestToolchainExecutionReceiptError.WrongRoleOrder)

receipt = _x86_fat32_receipt()
val first_alias = receipt.aliases[0]
receipt.aliases[0] = receipt.aliases[1]
receipt.aliases[1] = first_alias
expect(guest_toolchain_execution_receipt_v1_validate(receipt).unwrap_err()).to_equal(
    GuestToolchainExecutionReceiptError.WrongAliasOrder)
```

</details>

#### rejects mutation after the structural receipt is frozen

- Verify: rejects mutation after the structural receipt is frozen


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-010
# @req: REQ-009
step("Verify: rejects mutation after the structural receipt is frozen")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var receipt = _x86_fat32_receipt()
receipt.receipt_id = "toolchain-run-forged"
expect(guest_toolchain_execution_receipt_v1_validate(receipt).unwrap_err()).to_equal(
    GuestToolchainExecutionReceiptError.ReceiptPayloadDigestMismatch)
```

</details>

#### requires the full version-interpret-compile-load-delete-rerun workflow

- Verify: requires the full version-interpret-compile-load-delete-rerun workflow


<details>
<summary>Executable SSpec</summary>

Runnable source: 47 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-010
# @req: REQ-009
step("Verify: requires the full version-interpret-compile-load-delete-rerun workflow")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var receipt = _x86_fat32_receipt()
var version = receipt.roles[7]
version.argv = [version.tool_artifact_path, "version"]
receipt.roles[7] = version
expect(guest_toolchain_execution_receipt_v1_validate(receipt).unwrap_err()).to_equal(
    GuestToolchainExecutionReceiptError.InvalidArgv)

receipt = _x86_fat32_receipt()
var compile = receipt.roles[9]
compile.tool_artifact_sha256 = sha256_text("substituted-compiler")
receipt.roles[9] = compile
expect(guest_toolchain_execution_receipt_v1_validate(receipt).unwrap_err()).to_equal(
    GuestToolchainExecutionReceiptError.AliasDigestMismatch)

receipt = _x86_fat32_receipt()
var rerun = receipt.roles[11]
rerun.source_deleted_before_execution = false
receipt.roles[11] = rerun
expect(guest_toolchain_execution_receipt_v1_validate(receipt).unwrap_err()).to_equal(
    GuestToolchainExecutionReceiptError.InvalidSourceDeletionClaim)

receipt = _x86_fat32_receipt()
rerun = receipt.roles[11]
rerun.result_artifact_sha256 = sha256_text("substituted-compiled-artifact")
receipt.roles[11] = rerun
expect(guest_toolchain_execution_receipt_v1_validate(receipt).unwrap_err()).to_equal(
    GuestToolchainExecutionReceiptError.WorkflowArtifactMismatch)

receipt = _x86_fat32_receipt()
rerun = receipt.roles[11]
rerun.source_sha256 = sha256_text("different-deleted-source")
receipt.roles[11] = rerun
expect(guest_toolchain_execution_receipt_v1_validate(receipt).unwrap_err()).to_equal(
    GuestToolchainExecutionReceiptError.WorkflowSourceMismatch)

receipt = _x86_fat32_receipt()
rerun = receipt.roles[11]
rerun.expected_stdout = "different program\n"
rerun.observed_stdout = rerun.expected_stdout
rerun.observed_output_sha256 = guest_toolchain_role_output_sha256(rerun)
receipt.roles[11] = rerun
expect(guest_toolchain_execution_receipt_v1_validate(receipt).unwrap_err()).to_equal(
    GuestToolchainExecutionReceiptError.WorkflowOutputMismatch)
```

</details>

#### keeps the legacy host staging booleans fail closed even when all are true

- Verify: keeps the legacy host staging booleans fail closed even when all are true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-010
# @req: REQ-009
step("Verify: keeps the legacy host staging booleans fail closed even when all are true")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val detail = guest_toolchain_execution_gate_detail(true, true, true)
expect(detail).to_start_with("blocked:")
expect(detail).to_contain("authoritative target-native receipt producer")
expect(detail).to_contain("loader-owned consume-once token")
expect(detail.contains("READY")).to_be(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `44341f2ddf9a9eb2074bb55f5b91e9dda7fd751a05a3768f9b852dda35518663`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `44341f2ddf9a9eb2074bb55f5b91e9dda7fd751a05a3768f9b852dda35518663`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `44341f2ddf9a9eb2074bb55f5b91e9dda7fd751a05a3768f9b852dda35518663`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/toolchain/guest_toolchain_execution_gate_spec.spl
mirror: doc/06_spec/01_unit/os/toolchain/guest_toolchain_execution_gate_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/toolchain/guest_toolchain_execution_gate_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/toolchain/guest_toolchain_execution_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/toolchain/guest_toolchain_execution_gate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
