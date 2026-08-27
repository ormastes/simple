# smf_bounds_spec

> SMF Loader — bounds-check unit specs.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# smf_bounds_spec

SMF Loader — bounds-check unit specs.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #FS-EXEC-MULTIARCH-AC3 |
| Category | Kernel loader |
| Status | Active |
| Source | `test/01_unit/os/kernel/loader/smf_bounds_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

SMF Loader — bounds-check unit specs.
Verifies that _smf_copy_range (via smf_extract_executable_stub) fails closed
on truncated images and out-of-range sizes, and that the in_range guard in
byte_utils rejects overflow/negative inputs.

## Scenarios

### in_range bounds guard

#### accepts a zero-size range at offset zero

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts a zero-size range at offset zero
   - Expected: in_range(data, 0i64, 0i64) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("accepts a zero-size range at offset zero")
var data: [u8] = []
data.push(0u8)
expect(in_range(data, 0i64, 0i64)).to_equal(true)
```

</details>

#### accepts a range that exactly fills the buffer

- accepts a range that exactly fills the buffer
   - Expected: in_range(data, 0i64, 3i64) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("accepts a range that exactly fills the buffer")
var data: [u8] = []
data.push(1u8)
data.push(2u8)
data.push(3u8)
expect(in_range(data, 0i64, 3i64)).to_equal(true)
```

</details>

#### rejects a range that exceeds the buffer

- rejects a range that exceeds the buffer
   - Expected: in_range(data, 0i64, 3i64) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a range that exceeds the buffer")
var data: [u8] = []
data.push(1u8)
data.push(2u8)
expect(in_range(data, 0i64, 3i64)).to_equal(false)
```

</details>

#### rejects a negative offset

- rejects a negative offset
   - Expected: in_range(data, -1i64, 1i64) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a negative offset")
var data: [u8] = []
data.push(1u8)
expect(in_range(data, -1i64, 1i64)).to_equal(false)
```

</details>

#### rejects a negative size

- rejects a negative size
   - Expected: in_range(data, 0i64, -1i64) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a negative size")
var data: [u8] = []
data.push(1u8)
expect(in_range(data, 0i64, -1i64)).to_equal(false)
```

</details>

#### rejects an empty buffer with nonzero size

- rejects an empty buffer with nonzero size
   - Expected: in_range(data, 0i64, 1i64) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects an empty buffer with nonzero size")
var data: [u8] = []
expect(in_range(data, 0i64, 1i64)).to_equal(false)
```

</details>

### smf_extract_executable_stub — truncated image

#### rejects an image where stub_size exceeds bytes before the trailer

- rejects an image where stub_size exceeds bytes before the trailer
   - Expected: result.is_err() is true
   - Expected: result.err().unwrap() equals `SMF_ERR_MALFORMED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects an image where stub_size exceeds bytes before the trailer")
# declared stub_size=16 but only 4 ELF bytes precede the trailer
# stub_size(16) > header_offset(4) so callers return SMF_ERR_MALFORMED
val bytes = _truncated_smf(16i64, 4i64)
val result = smf_extract_executable_stub(bytes)
expect(result.is_err()).to_equal(true)
expect(result.err().unwrap()).to_equal(SMF_ERR_MALFORMED)
```

</details>

<details>
<summary>Advanced: rejects an image where the entire buffer is just the trailer (no room for stub)</summary>

#### rejects an image where the entire buffer is just the trailer (no room for stub)

- rejects an image where the entire buffer is just the trailer (no room for stub)
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects an image where the entire buffer is just the trailer (no room for stub)")
# stub_size=8 but header_offset=0 (trailer at offset 0, no leading bytes)
var trailer = _make_trailer(0x1000i64, 8i64)
# set stub_size to non-zero
trailer[52] = 8u8
val result = smf_extract_executable_stub(trailer)
expect(result.is_err()).to_equal(true)
```

</details>


</details>

#### accepts a well-formed SMF with a valid ELF stub

- accepts a well-formed SMF with a valid ELF stub
   - Expected: result.is_ok() is true
   - Expected: stub.len() equals `8`
   - Expected: stub[0] equals `0x7Fu8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("accepts a well-formed SMF with a valid ELF stub")
val bytes = _smf_with_elf_stub(8i64)
val result = smf_extract_executable_stub(bytes)
expect(result.is_ok()).to_equal(true)
val stub = result.unwrap()
expect(stub.len()).to_equal(8)
expect(stub[0]).to_equal(0x7Fu8)
```

</details>

### smf_extract_executable_stub — zero stub_size

#### returns SMF_ERR_MISSING_ELF when stub_size is zero

- returns SMF_ERR_MISSING_ELF when stub_size is zero
   - Expected: result.is_err() is true
   - Expected: result.err().unwrap() equals `SMF_ERR_MISSING_ELF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("returns SMF_ERR_MISSING_ELF when stub_size is zero")
# _make_trailer with stub_size=0 means no ELF stub declared
var trailer = _make_trailer(0x1000i64, 0i64)
val result = smf_extract_executable_stub(trailer)
expect(result.is_err()).to_equal(true)
expect(result.err().unwrap()).to_equal(SMF_ERR_MISSING_ELF)
```

</details>

### smf_extract_executable_stub_for_arch — truncated image arch-checked

#### rejects truncated image on x86_64 arch check

- rejects truncated image on x86_64 arch check
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects truncated image on x86_64 arch check")
val bytes = _truncated_smf(32i64, 4i64)
val result = smf_extract_executable_stub_for_arch(bytes, Architecture.X86_64)
expect(result.is_err()).to_equal(true)
```

</details>

#### rejects truncated image on arm64 arch check

- rejects truncated image on arm64 arch check
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects truncated image on arm64 arch check")
val bytes = _truncated_smf(32i64, 4i64)
val result = smf_extract_executable_stub_for_arch(bytes, Architecture.Arm64)
expect(result.is_err()).to_equal(true)
```

</details>

#### rejects truncated image on riscv64 arch check

- rejects truncated image on riscv64 arch check
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects truncated image on riscv64 arch check")
val bytes = _truncated_smf(32i64, 4i64)
val result = smf_extract_executable_stub_for_arch(bytes, Architecture.Riscv64)
expect(result.is_err()).to_equal(true)
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

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `73e4fcd190511944c78c536213442a569f10ab9b2fb9dab276d61f414c265300`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `73e4fcd190511944c78c536213442a569f10ab9b2fb9dab276d61f414c265300`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `73e4fcd190511944c78c536213442a569f10ab9b2fb9dab276d61f414c265300`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/os/kernel/loader/smf_bounds_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/loader/smf_bounds_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/loader/smf_bounds_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/loader/smf_bounds_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/loader/smf_bounds_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/kernel/loader/smf_bounds_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a zero-size range at offset zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/loader/smf_bounds_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a range that exactly fills the buffer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/loader/smf_bounds_spec.spl:113:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a range that exceeds the buffer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
