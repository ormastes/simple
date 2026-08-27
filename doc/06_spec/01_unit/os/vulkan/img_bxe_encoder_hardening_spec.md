# IMG BXE Submission Envelope Encoder — Hardening (Lane H2)

> The reader is an engineer asking: *can this envelope encoder be handed a job

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# IMG BXE Submission Envelope Encoder — Hardening (Lane H2)

The reader is an engineer asking: *can this envelope encoder be handed a job

## At a Glance

| Field | Value |
|-------|-------|
| Category | OS / GPU driver |
| Status | In Progress — hardening pass over the checked-in encoder; |
| Source | `test/01_unit/os/vulkan/img_bxe_encoder_hardening_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

The reader is an engineer asking: *can this envelope encoder be handed a job
descriptor a real PowerVR submission could never carry — an unknown job type,
a negative handle, a negative or overflowing stream length, a misaligned
offset — and still produce a packet, instead of a typed, field-named
rejection?*

## Scope and Preconditions

Pure computation, no GPU/board required. The firmware-consumed control-stream
CONTENTS remain an opaque blob per the architectural note at the top of
`encoder_img_bxe.spl` — this spec hardens the ENVELOPE only, per that file's
documented scope.

## Primary Workflow

Drive `img_bxe_job_validate`/`img_bxe_encode_job_checked`/
`img_bxe_check_alignment` with malformed job descriptors and confirm each
rejection names the offending field.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Field-width overflow | `stream_len` bounded to `IMG_BXE_MAX_STREAM_LEN` (32-bit) |
| Alignment | every offset this encoder produces must be a multiple of `IMG_BXE_DWORD_BYTES` |
| Payload/length agreement | `img_bxe_encode_job_checked` re-checks the packet's declared `length` against the computed payload dwords |
| Zero/empty decision | `stream_len == 0` and `sync_ops == []` are LEGAL — a degenerate but structurally valid submission |

## Recovery and Troubleshooting

A red here after touching `encoder_img_bxe.spl` means `img_bxe_job_validate`
stopped rejecting a case it used to, or the length-agreement check in
`img_bxe_encode_job_checked` was removed.

## Compatibility and Limitations

Does not touch `soc_profile.spl` or any capability flag. Hardening the
envelope does not resolve the firmware-content gap noted in the file header.

## Scenarios

### IMG BXE job_type validation

#### rejects an unknown job type, naming job_type

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects an unknown job type, naming job_type
- build a job with a job_type no PowerVR submission uses


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects an unknown job type, naming job_type")
step("build a job with a job_type no PowerVR submission uses")
val job = img_bxe_job_desc("raytrace", 1, 1, 0, [])
val result = img_bxe_job_validate(job)
assert_true(result.is_err())
assert_equal(result.unwrap_err().field_name, "job_type")
```

</details>

### IMG BXE stream_len validation

#### rejects a negative stream_len, naming stream_len

- rejects a negative stream_len, naming stream_len
- build a job with a negative stream length


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a negative stream_len, naming stream_len")
step("build a job with a negative stream length")
val job = img_bxe_job_desc("transfer", 1, 1, -1, [])
val result = img_bxe_job_validate(job)
assert_true(result.is_err())
assert_equal(result.unwrap_err().field_name, "stream_len")
```

</details>

#### rejects a stream_len beyond the 32-bit field maximum, naming stream_len

- rejects a stream_len beyond the 32-bit field maximum, naming stream_len
- build a job whose stream length overflows the length field


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a stream_len beyond the 32-bit field maximum, naming stream_len")
step("build a job whose stream length overflows the length field")
val job = img_bxe_job_desc("transfer", 1, 1, IMG_BXE_MAX_STREAM_LEN + 1, [])
val result = img_bxe_job_validate(job)
assert_true(result.is_err())
assert_equal(result.unwrap_err().field_name, "stream_len")
```

</details>

#### accepts a zero stream_len (legal degenerate submission)

- accepts a zero stream_len (legal degenerate submission)
- build a job with a zero-length control stream


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("accepts a zero stream_len (legal degenerate submission)")
step("build a job with a zero-length control stream")
val job = img_bxe_job_desc("transfer", 1, 0, 0, [])
assert_true(img_bxe_job_validate(job).is_ok())
```

</details>

### IMG BXE handle validation

#### rejects a negative context_handle, naming context_handle

- rejects a negative context_handle, naming context_handle
- build a job with a negative context handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a negative context_handle, naming context_handle")
step("build a job with a negative context handle")
val job = img_bxe_job_desc("transfer", -1, 1, 0, [])
val result = img_bxe_job_validate(job)
assert_true(result.is_err())
assert_equal(result.unwrap_err().field_name, "context_handle")
```

</details>

#### rejects a negative hwrt_data_set_handle, naming hwrt_data_set_handle

- rejects a negative hwrt_data_set_handle, naming hwrt_data_set_handle
- build a job with a negative HWRT dataset handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a negative hwrt_data_set_handle, naming hwrt_data_set_handle")
step("build a job with a negative HWRT dataset handle")
val job = img_bxe_job_desc("transfer", 1, -1, 0, [])
val result = img_bxe_job_validate(job)
assert_true(result.is_err())
assert_equal(result.unwrap_err().field_name, "hwrt_data_set_handle")
```

</details>

#### rejects a negative sync handle, naming the indexed sync_ops field

- rejects a negative sync handle, naming the indexed sync_ops field
- build a job whose second sync op has a negative handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a negative sync handle, naming the indexed sync_ops field")
step("build a job whose second sync op has a negative handle")
val ops = [img_bxe_sync_op(1, 0, 0), img_bxe_sync_op(-5, 0, 0)]
val job = img_bxe_uapi_job_desc("transfer", 1, 0, 0, 0, 0x2000, ops, 0, 0)
val result = img_bxe_job_validate(job)
assert_true(result.is_err())
assert_equal(result.unwrap_err().field_name, "sync_ops[1].handle")
```

</details>

#### accepts empty sync_ops (legal degenerate submission)

- accepts empty sync_ops (legal degenerate submission)
- build a job with no fences


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("accepts empty sync_ops (legal degenerate submission)")
step("build a job with no fences")
assert_true(img_bxe_job_validate(valid_job()).is_ok())
```

</details>

### IMG BXE alignment

#### rejects a misaligned offset, naming offset

- rejects a misaligned offset, naming offset
- check an offset that is not a multiple of the dword size


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a misaligned offset, naming offset")
step("check an offset that is not a multiple of the dword size")
val result = img_bxe_check_alignment(6)
assert_true(result.is_err())
assert_equal(result.unwrap_err().field_name, "offset")
```

</details>

#### accepts a dword-aligned offset

- accepts a dword-aligned offset
- check an offset that is a multiple of the dword size


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("accepts a dword-aligned offset")
step("check an offset that is a multiple of the dword size")
assert_true(img_bxe_check_alignment(12).is_ok())
```

</details>

### IMG BXE checked encode: length/payload agreement

#### produces a packet whose declared length equals the computed payload dwords

- produces a packet whose declared length equals the computed payload dwords
- encode a job with two sync ops


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("produces a packet whose declared length equals the computed payload dwords")
step("encode a job with two sync ops")
val ops = [img_bxe_sync_op(1, 0, 0), img_bxe_sync_op(2, 0, 5)]
val job = img_bxe_uapi_job_desc("geometry", 3, 0, 128, 0x1000, 0x2000, ops, 4, 0)
val packet = img_bxe_encode_job_checked(job).unwrap()
assert_equal(packet.length, img_bxe_job_payload_size(job) / 4)
```

</details>

#### refuses to encode a job img_bxe_job_validate would reject

- refuses to encode a job img_bxe_job_validate would reject
- attempt to encode a job with an unknown job type


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("refuses to encode a job img_bxe_job_validate would reject")
step("attempt to encode a job with an unknown job type")
val job = img_bxe_job_desc("raytrace", 1, 1, 0, [])
val result = img_bxe_encode_job_checked(job)
assert_true(result.is_err())
assert_equal(result.unwrap_err().field_name, "job_type")
```

</details>

### IMG BXE encoder sabotage

#### goes RED naming stream_len when the negative-stream_len guard is removed

- goes RED naming stream_len when the negative-stream_len guard is removed
- this scenario documents the sabotage performed out-of-band:
- removing the `job.stream_len < 0` check from img_bxe_job_validate
- re-assert the guard is present: a negative stream_len is still rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("goes RED naming stream_len when the negative-stream_len guard is removed")
step("this scenario documents the sabotage performed out-of-band:")
step("removing the `job.stream_len < 0` check from img_bxe_job_validate")
step("re-assert the guard is present: a negative stream_len is still rejected")
val job = img_bxe_job_desc("transfer", 1, 1, -1, [])
val result = img_bxe_job_validate(job)
assert_true(result.is_err())
assert_equal(result.unwrap_err().field_name, "stream_len")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-BOARD-VULKAN-001`
- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4fa2a2b14c9d3b6497cd1007465bd96d02e544f5d35f3054c3a281ba519ed289`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4fa2a2b14c9d3b6497cd1007465bd96d02e544f5d35f3054c3a281ba519ed289`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4fa2a2b14c9d3b6497cd1007465bd96d02e544f5d35f3054c3a281ba519ed289`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/vulkan/img_bxe_encoder_hardening_spec.spl
mirror: doc/06_spec/01_unit/os/vulkan/img_bxe_encoder_hardening_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=90
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=88; blocker cap makes effective=49
doc/06_spec/01_unit/os/vulkan/img_bxe_encoder_hardening_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/01_unit/os/vulkan/img_bxe_encoder_hardening_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/vulkan/img_bxe_encoder_hardening_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an unknown job type, naming job_type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/vulkan/img_bxe_encoder_hardening_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a negative stream_len, naming stream_len' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/vulkan/img_bxe_encoder_hardening_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a stream_len beyond the 32-bit field maximum, naming stream_len' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
