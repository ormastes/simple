# SCV and rendering file-read byte contract

> This executable system specification pins the byte-level contract of the two

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SCV and rendering file-read byte contract

This executable system specification pins the byte-level contract of the two

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SCV-IOREAD |
| Category | Stdlib |
| Status | In Progress |
| Plan | doc/03_plan/sys_test/scv_render_file_read_coverage.md |
| Source | `test/03_system/stdlib/io/scv_render_file_read_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

This executable system specification pins the byte-level contract of the two
canonical file-read entry points in `src/lib/nogc_sync_mut/io/file_ops.spl`, as
they were unified on 2026-08-16: `file_read_bytes` returns `[u8]` and
`file_read_bytes_i64` returns the same bytes in `[i64]` form. It is written for
stdlib, SCV, and rendering maintainers.

Both SCV and the font/rendering path read files as bytes. SCV reads through
`file_read_bytes_i64` and narrows to `[u8]`; the font path reads `[u8]`
directly. A return-type change to either entry point silently reshapes every
one of those readers, which is precisely what happened when the two shapes were
reconciled. These scenarios make that reshaping observable instead of latent.

## Scope and Preconditions

Scope is the byte fidelity of the read APIs themselves — length, element range,
agreement between the two shapes, and lossless round-trip of every byte value
including those above 0x7F, where an `[i64]`/`[u8]` confusion shows up first.

Preconditions: a writable scratch directory, and the in-repo font asset
`assets/fonts/google-fonts/ofl/bungee/Bungee-Regular.ttf`. Both are asserted,
never assumed. This specification is fail-closed: when a precondition cannot be
met it FAILS. No scenario skips, and no oracle is stubbed to pass, so an
environment that cannot satisfy the contract can never report green.

## Primary Workflow

Write a known byte sequence, read it back through both entry points, and assert
the two agree with each other and with what was written. Then read a real font
asset and assert the sfnt version bytes survive the read unchanged.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Canonical byte read | `file_read_bytes(path) -> [u8]`, the unified signature |
| Raw i64 byte read | `file_read_bytes_i64(path) -> [i64]`, the shape SCV consumes |
| Shape agreement | Both entry points must report identical bytes for one file |
| sfnt version | The four leading bytes `00 01 00 00` of a TrueType font |

## Related Specifications

- [file_read single return type](../../../01_unit/lib/nogc_sync_mut/file_read_single_return_type_spec.md) — static return-type guard for the text family (REQ-IOREAD-007/008)
- `test/01_unit/lib/nogc_sync_mut/file_read_bytes_single_definition_spec.spl` — static definition-count guard for the byte family

## Evidence and Provenance

Requirements REQ-IOREAD-001..006 are defined in
`doc/03_plan/sys_test/scv_render_file_read_coverage.md`. Contract pinned against
`src/lib/nogc_sync_mut/io/file_ops.spl` at the 2026-08-16 signature unification.

## Recovery and Troubleshooting

A failure in the agreement scenario means the two entry points have diverged
again — compare their return types before changing any caller. A failure only
for byte values above 0x7F indicates sign extension in the `[i64]` path.

## Compatibility and Limitations

Requires a qualified pure-Simple runtime. At the time of authoring no such
runtime was available in this workspace, so these scenarios are committed
unexecuted and are designed to run unchanged once one is. They must not be
reported as passing until they have actually run.

## Scenarios

### stdlib file-read byte contract

#### should return unsigned bytes from the canonical read

- should return unsigned bytes from the canonical read
- Read the fixture through the canonical byte entry point
- Verify length is preserved
   - Expected: bytes.len() equals `256`
- Verify every element is a value in 0..255 at its written index
   - Expected: mismatches equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-IOREAD-007/008
# @req REQ-IOREAD-001..006
# @req REQ-SSPEC-SYSTEM
step("should return unsigned bytes from the canonical read")
step("Read the fixture through the canonical byte entry point")
val bytes = file_read_bytes(scratch_file())
step("Verify length is preserved")
expect(bytes.len()).to_equal(256)
step("Verify every element is a value in 0..255 at its written index")
var i = 0
var mismatches = 0
while i < 256:
    if bytes[i].to_i64() != i:
        mismatches = mismatches + 1
    i = i + 1
expect(mismatches).to_equal(0)
```

</details>

#### should return the same bytes from the raw i64 read

- should return the same bytes from the raw i64 read
- Read the fixture through the raw i64 entry point
- Verify length is preserved
   - Expected: raw.len() equals `256`
- Verify no element carries sign extension above 0x7F
   - Expected: negatives equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-IOREAD-007/008
# @req REQ-IOREAD-001..006
# @req REQ-SSPEC-SYSTEM
step("should return the same bytes from the raw i64 read")
step("Read the fixture through the raw i64 entry point")
val raw = file_read_bytes_i64(scratch_file())
step("Verify length is preserved")
expect(raw.len()).to_equal(256)
step("Verify no element carries sign extension above 0x7F")
var i = 0
var negatives = 0
while i < 256:
    if raw[i] < 0:
        negatives = negatives + 1
    i = i + 1
expect(negatives).to_equal(0)
```

</details>

#### should agree between the unsigned and raw read shapes

- should agree between the unsigned and raw read shapes
- Read the same fixture through both entry points
- Verify both shapes report the same length
   - Expected: bytes.len() equals `raw.len()`
- Verify both shapes report the same byte at every index
   - Expected: disagreements equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-IOREAD-007/008
# @req REQ-IOREAD-001..006
# @req REQ-SSPEC-SYSTEM
step("should agree between the unsigned and raw read shapes")
step("Read the same fixture through both entry points")
val bytes = file_read_bytes(scratch_file())
val raw = file_read_bytes_i64(scratch_file())
step("Verify both shapes report the same length")
expect(bytes.len()).to_equal(raw.len())
step("Verify both shapes report the same byte at every index")
var i = 0
var disagreements = 0
while i < bytes.len():
    if bytes[i].to_i64() != (raw[i] & 0xFF):
        disagreements = disagreements + 1
    i = i + 1
expect(disagreements).to_equal(0)
```

</details>

### rendering font read byte contract

#### should preserve the sfnt version bytes of a real font

- requires the in-repo font asset
- Confirm the font asset is present
   - Expected: file_exists(font_asset()) is true
- should preserve the sfnt version bytes of a real font
- Read the font asset as bytes
- Verify the read returned a non-empty font body
- Verify the leading sfnt version bytes are 00 01 00 00
   - Expected: font[0].to_i64() equals `0`
   - Expected: font[1].to_i64() equals `1`
   - Expected: font[2].to_i64() equals `0`
   - Expected: font[3].to_i64() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires the in-repo font asset")
step("Confirm the font asset is present")
require_font_asset()
expect(file_exists(font_asset())).to_equal(true)

# @req REQ-SSPEC-SYSTEM
step("should preserve the sfnt version bytes of a real font")
step("Read the font asset as bytes")
val font = file_read_bytes(font_asset())
step("Verify the read returned a non-empty font body")
expect(font.len()).to_be_greater_than(4)
step("Verify the leading sfnt version bytes are 00 01 00 00")
expect(font[0].to_i64()).to_equal(0)
expect(font[1].to_i64()).to_equal(1)
expect(font[2].to_i64()).to_equal(0)
expect(font[3].to_i64()).to_equal(0)
```

</details>

### text and byte read agreement

#### should report the same ASCII content through both read families

- should report the same ASCII content through both read families
- Write a known ASCII payload
- Read it through the text family
- Read it through the byte family
- Verify the two families agree on length and content
   - Expected: as_text equals `SCV`
   - Expected: as_bytes.len() equals `3`
   - Expected: as_bytes[0].to_i64() equals `83`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should report the same ASCII content through both read families")
step("Write a known ASCII payload")
dir_create_all(scratch_dir())
val ascii_path = scratch_dir() + "/ascii.txt"
var ascii: [u8] = []
ascii.push(83.to_u8())
ascii.push(67.to_u8())
ascii.push(86.to_u8())
val wrote = file_write_bytes(ascii_path, ascii)
if not wrote:
    fail("precondition failed: could not write " + ascii_path)
step("Read it through the text family")
val as_text = file_read_text(ascii_path)
step("Read it through the byte family")
val as_bytes = file_read_bytes(ascii_path)
step("Verify the two families agree on length and content")
expect(as_text).to_equal("SCV")
expect(as_bytes.len()).to_equal(3)
expect(as_bytes[0].to_i64()).to_equal(83)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/sys_test/scv_render_file_read_coverage.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-IOREAD-001..006`
- `REQ-IOREAD-007/008`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `61ed715332e53cef49011ec24bb3bd363184101f7cae4389b19276542e97684f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `61ed715332e53cef49011ec24bb3bd363184101f7cae4389b19276542e97684f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `61ed715332e53cef49011ec24bb3bd363184101f7cae4389b19276542e97684f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **83/100**; blockers: **0**.

SSpec documentization score: 83/100
source: test/03_system/stdlib/io/scv_render_file_read_contract_spec.spl
mirror: doc/06_spec/03_system/stdlib/io/scv_render_file_read_contract_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=65 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=90
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/stdlib/io/scv_render_file_read_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/03_system/stdlib/io/scv_render_file_read_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/stdlib/io/scv_render_file_read_contract_spec.spl:135:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'writes a scratch fixture covering every byte value' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/stdlib/io/scv_render_file_read_contract_spec.spl:149:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should return unsigned bytes from the canonical read' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/stdlib/io/scv_render_file_read_contract_spec.spl:149:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should return unsigned bytes from the canonical read' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/stdlib/io/scv_render_file_read_contract_spec.spl:166:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should return the same bytes from the raw i64 read' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/stdlib/io/scv_render_file_read_contract_spec.spl:166:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should return the same bytes from the raw i64 read' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/stdlib/io/scv_render_file_read_contract_spec.spl:183:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should agree between the unsigned and raw read shapes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/stdlib/io/scv_render_file_read_contract_spec.spl:183:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should agree between the unsigned and raw read shapes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/stdlib/io/scv_render_file_read_contract_spec.spl:216:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve the sfnt version bytes of a real font' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/stdlib/io/scv_render_file_read_contract_spec.spl:236:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should report the same ASCII content through both read families' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
