# Safetensors Specification

> Tests covering parse_safetensors_header — happy path (A2), parse_safetensors_header — error paths.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Safetensors Specification

## Scenarios

### parse_safetensors_header — happy path (A2)

#### returns Ok for the tiny 2-tensor fixture

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns Ok for the tiny 2-tensor fixture
   - Expected: r.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns Ok for the tiny 2-tensor fixture")
val buf = build_tiny_safetensors()
val r = parse_safetensors_header(buf)
expect(r.is_ok()).to_equal(true)
```

</details>

#### records the 8-byte header length prefix value

- records the 8-byte header length prefix value


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("records the 8-byte header length prefix value")
val buf = build_tiny_safetensors()
val r = parse_safetensors_header(buf)
val h = r.unwrap()
expect(h.header_byte_len).to_be_greater_than(100)
```

</details>

#### extracts exactly two tensor entries

- extracts exactly two tensor entries
   - Expected: h.tensors.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("extracts exactly two tensor entries")
val buf = build_tiny_safetensors()
val h = parse_safetensors_header(buf).unwrap()
expect(h.tensors.len()).to_equal(2)
```

</details>

#### first tensor is named 'w' with dtype F32

- first tensor is named 'w' with dtype F32
   - Expected: w.name equals `w`
   - Expected: w.dtype equals `F32`
   - Expected: w.dtype_tag equals `Dtype.F32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("first tensor is named 'w' with dtype F32")
val buf = build_tiny_safetensors()
val h = parse_safetensors_header(buf).unwrap()
val w = h.tensors[0]
expect(w.name).to_equal("w")
expect(w.dtype).to_equal("F32")
expect(w.dtype_tag).to_equal(Dtype.F32)
```

</details>

#### first tensor has shape [2,2] and data_offsets [0,16]

- first tensor has shape [2,2] and data_offsets [0,16]
   - Expected: w.shape.len() equals `2`
   - Expected: w.shape[0] equals `2`
   - Expected: w.shape[1] equals `2`
   - Expected: w.offset equals `0`
   - Expected: w.length equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("first tensor has shape [2,2] and data_offsets [0,16]")
val buf = build_tiny_safetensors()
val h = parse_safetensors_header(buf).unwrap()
val w = h.tensors[0]
expect(w.shape.len()).to_equal(2)
expect(w.shape[0]).to_equal(2)
expect(w.shape[1]).to_equal(2)
expect(w.offset).to_equal(0)
expect(w.length).to_equal(16)
```

</details>

#### second tensor is named 'b' with dtype I64

- second tensor is named 'b' with dtype I64
   - Expected: b.name equals `b`
   - Expected: b.dtype equals `I64`
   - Expected: b.dtype_tag equals `Dtype.I64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("second tensor is named 'b' with dtype I64")
val buf = build_tiny_safetensors()
val h = parse_safetensors_header(buf).unwrap()
val b = h.tensors[1]
expect(b.name).to_equal("b")
expect(b.dtype).to_equal("I64")
expect(b.dtype_tag).to_equal(Dtype.I64)
```

</details>

### parse_safetensors_header — error paths

#### rejects buffers shorter than 8 bytes as TruncatedHeader

- rejects buffers shorter than 8 bytes as TruncatedHeader
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects buffers shorter than 8 bytes as TruncatedHeader")
var buf: [u8] = []
buf.push(0 as u8)
buf.push(0 as u8)
val r = parse_safetensors_header(buf)
expect(r.is_err()).to_equal(true)
```

</details>

#### rejects a length prefix that overruns the buffer

- rejects a length prefix that overruns the buffer
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a length prefix that overruns the buffer")
# Prefix claims 999 bytes of JSON but buffer is only 8 bytes long.
var buf: [u8] = []
buf = push_u64_le(buf, 999)
val r = parse_safetensors_header(buf)
expect(r.is_err()).to_equal(true)
```

</details>

#### rejects malformed JSON header as MalformedJson

- rejects malformed JSON header as MalformedJson
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects malformed JSON header as MalformedJson")
val bad = "not-a-json-object"
var buf: [u8] = []
buf = push_u64_le(buf, bad.len() as i64)
buf = push_ascii(buf, bad)
val r = parse_safetensors_header(buf)
expect(r.is_err()).to_equal(true)
```

</details>

#### rejects unknown dtype strings

- rejects unknown dtype strings
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects unknown dtype strings")
val j = "{\"x\":{\"dtype\":\"WEIRD\",\"shape\":[1],\"data_offsets\":[0,4]}}"
var buf: [u8] = []
buf = push_u64_le(buf, j.len() as i64)
buf = push_ascii(buf, j)
# Pad 4 bytes payload.
var i = 0
while i < 4:
    buf.push(0 as u8)
    i = i + 1
val r = parse_safetensors_header(buf)
expect(r.is_err()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/slang/model_executor/model_loader/safetensors_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering parse_safetensors_header — happy path (A2), parse_safetensors_header — error paths.
- parse_safetensors_header — happy path (A2)
- parse_safetensors_header — error paths

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `309d43bee719b9067108a6c09931f5d06360557e739a6c06d8dd3aecbe9d14d6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `309d43bee719b9067108a6c09931f5d06360557e739a6c06d8dd3aecbe9d14d6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `309d43bee719b9067108a6c09931f5d06360557e739a6c06d8dd3aecbe9d14d6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/gc_async_mut/slang/model_executor/model_loader/safetensors_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/slang/model_executor/model_loader/safetensors_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/slang/model_executor/model_loader/safetensors_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/slang/model_executor/model_loader/safetensors_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/slang/model_executor/model_loader/safetensors_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/slang/model_executor/model_loader/safetensors_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns Ok for the tiny 2-tensor fixture' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/slang/model_executor/model_loader/safetensors_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records the 8-byte header length prefix value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/slang/model_executor/model_loader/safetensors_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts exactly two tensor entries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
