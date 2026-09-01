# DBD filesystem launch admission

> Proves that filesystem presence alone cannot start DBD: the canonical image

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DBD filesystem launch admission

Proves that filesystem presence alone cannot start DBD: the canonical image

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/apps/dbd/dbd_launch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Proves that filesystem presence alone cannot start DBD: the canonical image
must carry loader verification evidence, arguments are forbidden so secrets
cannot enter process metadata, and production security owners remain the final
readiness gate.

## Scenarios

### DBD canonical filesystem artifact

#### reaches the security-owner gate only with complete loader evidence

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reaches the security-owner gate only with complete loader evidence
   - Expected: admission.blocker equals `DBD_BOOT_CREDENTIAL_OWNER_BLOCKER`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reaches the security-owner gate only with complete loader evidence")
val admission = dbd_admit_filesystem_launch_v1(_artifact(), [])
expect(admission.status).to_equal(
    DbdFilesystemLaunchStatusV1.SecurityOwnersBlocked)
expect(admission.blocker).to_equal(DBD_BOOT_CREDENTIAL_OWNER_BLOCKER)
```

</details>

#### rejects aliases, empty images, oversized images, and unverified format

- rejects aliases, empty images, oversized images, and unverified format


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects aliases, empty images, oversized images, and unverified format")
var alias = _artifact()
alias.path = "/tmp/dbd"
expect(dbd_admit_filesystem_launch_v1(alias, []).status).to_equal(
    DbdFilesystemLaunchStatusV1.ArtifactRejected)
var empty = _artifact()
empty.byte_length = 0
expect(dbd_admit_filesystem_launch_v1(empty, []).status).to_equal(
    DbdFilesystemLaunchStatusV1.ArtifactRejected)
var oversized = _artifact()
oversized.byte_length = DBD_MAX_FILESYSTEM_IMAGE_BYTES_V1 + 1
expect(dbd_admit_filesystem_launch_v1(oversized, []).status).to_equal(
    DbdFilesystemLaunchStatusV1.ArtifactRejected)
var unverified = _artifact()
unverified.executable_format_verified = false
expect(dbd_admit_filesystem_launch_v1(unverified, []).status).to_equal(
    DbdFilesystemLaunchStatusV1.ArtifactRejected)
```

</details>

#### requires one canonical lowercase SHA-256 receipt

- requires one canonical lowercase SHA-256 receipt


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires one canonical lowercase SHA-256 receipt")
var short_digest = _artifact()
short_digest.sha256_hex = "abcd"
expect(dbd_admit_filesystem_launch_v1(
    short_digest, []).status).to_equal(
    DbdFilesystemLaunchStatusV1.ArtifactRejected)
var uppercase_digest = _artifact()
uppercase_digest.sha256_hex =
    "0123456789ABCDEF0123456789abcdef0123456789abcdef0123456789abcdef"
expect(dbd_admit_filesystem_launch_v1(
    uppercase_digest, []).status).to_equal(
    DbdFilesystemLaunchStatusV1.ArtifactRejected)
```

</details>

### DBD filesystem launch arguments

#### rejects every argument before production readiness admission

- rejects every argument before production readiness admission
   - Expected: admission.blocker equals `dbd-launch-arguments-forbidden`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects every argument before production readiness admission")
val admission = dbd_admit_filesystem_launch_v1(
    _artifact(), ["--credential=must-not-enter-process-metadata"])
expect(admission.status).to_equal(
    DbdFilesystemLaunchStatusV1.ArgumentsRejected)
expect(admission.blocker).to_equal("dbd-launch-arguments-forbidden")
```

</details>

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

- Canonical SPipe generation for source `a78e39bc7d1ec2f882e2e0340b2ab45fbddac332fb49e210721c8f83df0b452b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a78e39bc7d1ec2f882e2e0340b2ab45fbddac332fb49e210721c8f83df0b452b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a78e39bc7d1ec2f882e2e0340b2ab45fbddac332fb49e210721c8f83df0b452b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/apps/dbd/dbd_launch_spec.spl
mirror: doc/06_spec/01_unit/os/apps/dbd/dbd_launch_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/apps/dbd/dbd_launch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/apps/dbd/dbd_launch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/apps/dbd/dbd_launch_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reaches the security-owner gate only with complete loader evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/apps/dbd/dbd_launch_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects aliases, empty images, oversized images, and unverified format' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/apps/dbd/dbd_launch_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires one canonical lowercase SHA-256 receipt' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
