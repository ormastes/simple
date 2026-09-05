# Simpleos Executable Admission V1 Specification

> Tests covering SimpleOS executable admission and image-handle contracts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Executable Admission V1 Specification

## Scenarios

### SimpleOS executable admission and image-handle contracts

#### validates a closed admission binding

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- validates a closed admission binding
   - Expected: check.ok is true
   - Expected: check.error equals `ExecutableContractErrorV1.None`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates a closed admission binding")
val check = executable_admission_validate(valid_admission())
expect(check.ok).to_equal(true)
expect(check.error).to_equal(ExecutableContractErrorV1.None)
```

</details>

#### fails closed for wildcard targets and malformed digests

- fails closed for wildcard targets and malformed digests
   - Expected: wildcard_check.ok is false
   - Expected: wildcard_check.error equals `ExecutableContractErrorV1.InvalidTarget`
   - Expected: digest_check.ok is false
   - Expected: digest_check.error equals `ExecutableContractErrorV1.InvalidDigest`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed for wildcard targets and malformed digests")
val admission = admission_record(
    ManifestTarget(os: "any", arch: "x86_64", abi: "simpleos"),
    ExecutableAdmissionDecisionV1.Admitted,
    ""
)
val wildcard_check = executable_admission_validate(admission)
expect(wildcard_check.ok).to_equal(false)
expect(wildcard_check.error).to_equal(ExecutableContractErrorV1.InvalidTarget)

val malformed = ExecutableAdmissionV1(
    schema_version: executable_admission_schema_version(),
    admission_id: "admission-1",
    decision: ExecutableAdmissionDecisionV1.Admitted,
    rejection_reason: "",
    image_hash: "not-a-digest",
    manifest_hash: digest_b(),
    kernel_hash: digest_a(),
    trust_root_hash: digest_b(),
    trust_epoch: 7u64,
    target: target(),
    firmware_profile: "uefi-secure",
    compiler_identity: "compiler-1",
    source_identity: "source-1",
    config_identity: "config-1",
    mount_id: 3u64,
    mount_generation: 8u64,
    file_id: 4u64,
    file_generation: 9u64,
    effective_capabilities: 5u32
)
val digest_check = executable_admission_validate(malformed)
expect(digest_check.ok).to_equal(false)
expect(digest_check.error).to_equal(ExecutableContractErrorV1.InvalidDigest)
```

</details>

#### keeps rejected admissions typed and non-loadable

- keeps rejected admissions typed and non-loadable
   - Expected: admission_check.ok is true
   - Expected: binding_check.ok is false
   - Expected: binding_check.error equals `ExecutableContractErrorV1.AdmissionMismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps rejected admissions typed and non-loadable")
val rejected = admission_record(
    target(), ExecutableAdmissionDecisionV1.Rejected, "trust-denied")
val admission_check = executable_admission_validate(rejected)
expect(admission_check.ok).to_equal(true)
val binding_check = executable_image_handle_matches_admission(
    valid_handle(), rejected)
expect(binding_check.ok).to_equal(false)
expect(binding_check.error).to_equal(ExecutableContractErrorV1.AdmissionMismatch)
```

</details>

#### rejects zero admission identities and generations

- rejects zero admission identities and generations
   - Expected: mount_check.ok is false
   - Expected: mount_check.error equals `ExecutableContractErrorV1.InvalidGeneration`
   - Expected: file_check.ok is false
   - Expected: file_check.error equals `ExecutableContractErrorV1.InvalidGeneration`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects zero admission identities and generations")
var zero_mount = valid_admission()
zero_mount.mount_id = 0u64
val mount_check = executable_admission_validate(zero_mount)
expect(mount_check.ok).to_equal(false)
expect(mount_check.error).to_equal(ExecutableContractErrorV1.InvalidGeneration)

var zero_file_generation = valid_admission()
zero_file_generation.file_generation = 0u64
val file_check = executable_admission_validate(zero_file_generation)
expect(file_check.ok).to_equal(false)
expect(file_check.error).to_equal(ExecutableContractErrorV1.InvalidGeneration)
```

</details>

#### validates bounded ranges and binds an open handle to admission

- validates bounded ranges and binds an open handle to admission
   - Expected: handle_check.ok is true
   - Expected: binding_check.ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates bounded ranges and binds an open handle to admission")
val handle_check = executable_image_handle_validate(valid_handle())
expect(handle_check.ok).to_equal(true)
val binding_check = executable_image_handle_matches_admission(
    valid_handle(), valid_admission())
expect(binding_check.ok).to_equal(true)
```

</details>

#### reports an invalid handle target as InvalidTarget

- reports an invalid handle target as InvalidTarget
   - Expected: check.ok is false
   - Expected: check.error equals `ExecutableContractErrorV1.InvalidTarget`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports an invalid handle target as InvalidTarget")
val invalid_target = handle_with_target(
    ManifestTarget(os: "any", arch: "x86_64", abi: "simpleos"))
val check = executable_image_handle_validate(invalid_target)
expect(check.ok).to_equal(false)
expect(check.error).to_equal(ExecutableContractErrorV1.InvalidTarget)
```

</details>

#### rejects overlapping ranges and generation drift

- rejects overlapping ranges and generation drift
   - Expected: overlap_check.ok is false
   - Expected: overlap_check.error equals `ExecutableContractErrorV1.InvalidRangeOverlap`
   - Expected: wx_check.ok is false
   - Expected: wx_check.error equals `ExecutableContractErrorV1.InvalidRange`
   - Expected: drift_check.ok is false
   - Expected: drift_check.error equals `ExecutableContractErrorV1.AdmissionMismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects overlapping ranges and generation drift")
val overlap_check = executable_image_handle_validate(
    handle_with_ranges(overlapping_ranges()))
expect(overlap_check.ok).to_equal(false)
expect(overlap_check.error).to_equal(ExecutableContractErrorV1.InvalidRangeOverlap)

val wx_check = executable_image_handle_validate(handle_with_ranges(wx_ranges()))
expect(wx_check.ok).to_equal(false)
expect(wx_check.error).to_equal(ExecutableContractErrorV1.InvalidRange)

var handle = valid_handle()
handle.mount_generation = 99u64
val drift_check = executable_image_handle_matches_admission(
    handle, valid_admission())
expect(drift_check.ok).to_equal(false)
expect(drift_check.error).to_equal(ExecutableContractErrorV1.AdmissionMismatch)
```

</details>

#### rejects empty ranges, zero identities, oversize images, and bad counters

- rejects empty ranges, zero identities, oversize images, and bad counters
   - Expected: empty_check.ok is false
   - Expected: empty_check.error equals `ExecutableContractErrorV1.InvalidRangeCount`
   - Expected: id_check.ok is false
   - Expected: id_check.error equals `ExecutableContractErrorV1.InvalidOpaqueIdentity`
   - Expected: mount_id_check.ok is false
   - Expected: mount_id_check.error equals `ExecutableContractErrorV1.InvalidOpaqueIdentity`
   - Expected: file_id_check.ok is false
   - Expected: file_id_check.error equals `ExecutableContractErrorV1.InvalidOpaqueIdentity`
   - Expected: generation_check.ok is false
   - Expected: generation_check.error equals `ExecutableContractErrorV1.InvalidGeneration`
   - Expected: mount_generation_check.ok is false
   - Expected: mount_generation_check.error equals `ExecutableContractErrorV1.InvalidGeneration`
   - Expected: size_check.ok is false
   - Expected: size_check.error equals `ExecutableContractErrorV1.InvalidImageSize`
   - Expected: read_count_check.ok is false
   - Expected: read_count_check.error equals `ExecutableContractErrorV1.InvalidReadCounters`
   - Expected: read_bytes_check.ok is false
   - Expected: read_bytes_check.error equals `ExecutableContractErrorV1.InvalidReadCounters`


<details>
<summary>Executable SSpec</summary>

Runnable source: 53 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects empty ranges, zero identities, oversize images, and bad counters")
val empty_check = executable_image_handle_validate(handle_with_ranges([]))
expect(empty_check.ok).to_equal(false)
expect(empty_check.error).to_equal(ExecutableContractErrorV1.InvalidRangeCount)

var zero_id = valid_handle()
zero_id.open_handle_id = 0u64
val id_check = executable_image_handle_validate(zero_id)
expect(id_check.ok).to_equal(false)
expect(id_check.error).to_equal(ExecutableContractErrorV1.InvalidOpaqueIdentity)

var zero_mount_id = valid_handle()
zero_mount_id.mount_id = 0u64
val mount_id_check = executable_image_handle_validate(zero_mount_id)
expect(mount_id_check.ok).to_equal(false)
expect(mount_id_check.error).to_equal(ExecutableContractErrorV1.InvalidOpaqueIdentity)

var zero_file_id = valid_handle()
zero_file_id.file_id = 0u64
val file_id_check = executable_image_handle_validate(zero_file_id)
expect(file_id_check.ok).to_equal(false)
expect(file_id_check.error).to_equal(ExecutableContractErrorV1.InvalidOpaqueIdentity)

var zero_generation = valid_handle()
zero_generation.file_generation = 0u64
val generation_check = executable_image_handle_validate(zero_generation)
expect(generation_check.ok).to_equal(false)
expect(generation_check.error).to_equal(ExecutableContractErrorV1.InvalidGeneration)

var zero_mount_generation = valid_handle()
zero_mount_generation.mount_generation = 0u64
val mount_generation_check = executable_image_handle_validate(zero_mount_generation)
expect(mount_generation_check.ok).to_equal(false)
expect(mount_generation_check.error).to_equal(ExecutableContractErrorV1.InvalidGeneration)

var oversize = valid_handle()
oversize.size_bytes = executable_image_max_bytes() + 1u64
val size_check = executable_image_handle_validate(oversize)
expect(size_check.ok).to_equal(false)
expect(size_check.error).to_equal(ExecutableContractErrorV1.InvalidImageSize)

var too_many_reads = valid_handle()
too_many_reads.read_count = executable_image_max_read_count() + 1u64
val read_count_check = executable_image_handle_validate(too_many_reads)
expect(read_count_check.ok).to_equal(false)
expect(read_count_check.error).to_equal(ExecutableContractErrorV1.InvalidReadCounters)

var too_many_bytes = valid_handle()
too_many_bytes.read_bytes = too_many_bytes.size_bytes + 1u64
val read_bytes_check = executable_image_handle_validate(too_many_bytes)
expect(read_bytes_check.ok).to_equal(false)
expect(read_bytes_check.error).to_equal(ExecutableContractErrorV1.InvalidReadCounters)
```

</details>

#### consumes a valid handle once without mutating the source value

- consumes a valid handle once without mutating the source value
   - Expected: first.ok is true
   - Expected: first.reason equals `ok`
   - Expected: first.handle.consumed is true
   - Expected: original.consumed is false
   - Expected: second.ok is false
   - Expected: second.reason equals `already-consumed`
   - Expected: second.handle.consumed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("consumes a valid handle once without mutating the source value")
val original = valid_handle()
val first = executable_image_handle_consume_once(original)
expect(first.ok).to_equal(true)
expect(first.reason).to_equal("ok")
expect(first.handle.consumed).to_equal(true)
expect(original.consumed).to_equal(false)

val second = executable_image_handle_consume_once(first.handle)
expect(second.ok).to_equal(false)
expect(second.reason).to_equal("already-consumed")
expect(second.handle.consumed).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/contracts/execution/simpleos_executable_admission_v1_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS executable admission and image-handle contracts.
- SimpleOS executable admission and image-handle contracts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `f73a660cee9a1fd56d3ea9d4728a4ef41ca8e13731064765c3a0cf98464a41bb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f73a660cee9a1fd56d3ea9d4728a4ef41ca8e13731064765c3a0cf98464a41bb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f73a660cee9a1fd56d3ea9d4728a4ef41ca8e13731064765c3a0cf98464a41bb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/contracts/execution/simpleos_executable_admission_v1_spec.spl
mirror: doc/06_spec/01_unit/lib/common/contracts/execution/simpleos_executable_admission_v1_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/contracts/execution/simpleos_executable_admission_v1_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/contracts/execution/simpleos_executable_admission_v1_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/contracts/execution/simpleos_executable_admission_v1_spec.spl:144:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validates a closed admission binding' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/contracts/execution/simpleos_executable_admission_v1_spec.spl:151:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed for wildcard targets and malformed digests' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/contracts/execution/simpleos_executable_admission_v1_spec.spl:188:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps rejected admissions typed and non-loadable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
