# SMF loader hardening — malformed / hostile envelopes (Lane HARDEN-ROBUST)

> TEST-ONLY: exercises the pure SMF envelope parser/extractor

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SMF loader hardening — malformed / hostile envelopes (Lane HARDEN-ROBUST)

TEST-ONLY: exercises the pure SMF envelope parser/extractor

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/loader/smf_loader_hardening_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

TEST-ONLY: exercises the pure SMF envelope parser/extractor
(src/os/kernel/loader/smf.spl) with wrong magic, wrong role/arch/ABI bytes, a
truncated trailer, and bogus stub offsets, asserting every path fails closed
with the correct `SMF_ERR_*` classification or a nil header — never a crash,
never an out-of-bounds copy, never a stub accepted without ELF magic.

Byte fixtures are built by concatenation (no in-place index assignment) so the
whole spec runs green under `simple run` (seed interpreter). A single valid
envelope is included as a positive control so the rejections are meaningful.

## Scenarios

### smf magic/header detection: fail closed

#### an all-zero 128-byte blob has no SMF magic or header

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- an all-zero 128-byte blob has no SMF magic or header
   - Expected: smf_check_magic(a) is false
   - Expected: smf_has_header(a) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an all-zero 128-byte blob has no SMF magic or header")
val a = _zeros(128)
expect(smf_check_magic(a)).to_equal(false)
expect(smf_has_header(a)).to_equal(false)
val h = smf_parse_header(a)
assert_true(h == nil)
```

</details>

#### a bare ELF file is not mistaken for an SMF envelope

- a bare ELF file is not mistaken for an SMF envelope
   - Expected: smf_has_header(a) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a bare ELF file is not mistaken for an SMF envelope")
val a = _elf_stub(64)
expect(smf_has_header(a)).to_equal(false)
```

</details>

#### a tiny (<4 byte) blob is rejected, not OOB

- a tiny (<4 byte) blob is rejected, not OOB
   - Expected: smf_has_header(a) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a tiny (<4 byte) blob is rejected, not OOB")
val a = _zeros(2)
expect(smf_has_header(a)).to_equal(false)
assert_true(smf_parse_header(a) == nil)
```

</details>

### smf parse: truncated trailer

#### magic present but the 128-byte trailer does not fit -> nil header

- magic present but the 128-byte trailer does not fit -> nil header
   - Expected: _bytes_err(smf_extract_executable_stub(a)) equals `SMF_ERR_MALFORMED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("magic present but the 128-byte trailer does not fit -> nil header")
# magic at offset 0, total length 64 (< 128): header_offset==0 but
# off+128 > len, so parse must refuse.
val a = [83 as u8, 77 as u8, 70 as u8, 0 as u8] + _zeros(60)
assert_true(smf_parse_header(a) == nil)
expect(_bytes_err(smf_extract_executable_stub(a))).to_equal("SMF_ERR_MALFORMED")
```

</details>

### smf executable extraction: metadata rejection (fail closed)

#### wrong magic -> SMF_ERR_MALFORMED

- wrong magic -> SMF_ERR_MALFORMED
   - Expected: _bytes_err(smf_extract_executable_stub(_zeros(256))) equals `SMF_ERR_MALFORMED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wrong magic -> SMF_ERR_MALFORMED")
expect(_bytes_err(smf_extract_executable_stub(_zeros(256)))).to_equal("SMF_ERR_MALFORMED")
```

</details>

#### wrong role (library role on an executable request) -> SMF_ERR_WRONG_ROLE

- wrong role (library role on an executable request) -> SMF_ERR_WRONG_ROLE
   - Expected: _bytes_err(smf_extract_executable_stub(_smf_exe(64, 2, 1, 1))) equals `SMF_ERR_WRONG_ROLE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wrong role (library role on an executable request) -> SMF_ERR_WRONG_ROLE")
expect(_bytes_err(smf_extract_executable_stub(_smf_exe(64, 2, 1, 1)))).to_equal("SMF_ERR_WRONG_ROLE")
```

</details>

#### wrong ABI byte -> SMF_ERR_ABI_MISMATCH

- wrong ABI byte -> SMF_ERR_ABI_MISMATCH
   - Expected: _bytes_err(smf_extract_executable_stub(_smf_exe(64, 1, 1, 2))) equals `SMF_ERR_ABI_MISMATCH`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wrong ABI byte -> SMF_ERR_ABI_MISMATCH")
expect(_bytes_err(smf_extract_executable_stub(_smf_exe(64, 1, 1, 2)))).to_equal("SMF_ERR_ABI_MISMATCH")
```

</details>

#### non-positive stub size -> SMF_ERR_MISSING_ELF

- non-positive stub size -> SMF_ERR_MISSING_ELF
   - Expected: _bytes_err(smf_extract_executable_stub(_smf_exe(0, 1, 1, 1))) equals `SMF_ERR_MISSING_ELF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("non-positive stub size -> SMF_ERR_MISSING_ELF")
expect(_bytes_err(smf_extract_executable_stub(_smf_exe(0, 1, 1, 1)))).to_equal("SMF_ERR_MISSING_ELF")
```

</details>

#### stub size larger than the header offset -> SMF_ERR_MALFORMED

- stub size larger than the header offset -> SMF_ERR_MALFORMED
   - Expected: _bytes_err(smf_extract_executable_stub(_smf_exe(200, 1, 1, 1))) equals `SMF_ERR_MALFORMED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stub size larger than the header offset -> SMF_ERR_MALFORMED")
expect(_bytes_err(smf_extract_executable_stub(_smf_exe(200, 1, 1, 1)))).to_equal("SMF_ERR_MALFORMED")
```

</details>

#### declared stub carries no ELF magic -> SMF_ERR_MISSING_ELF

- declared stub carries no ELF magic -> SMF_ERR_MISSING_ELF
   - Expected: _bytes_err(smf_extract_executable_stub(a)) equals `SMF_ERR_MISSING_ELF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declared stub carries no ELF magic -> SMF_ERR_MISSING_ELF")
val a = _zeros(64) + _smf_trailer(0x1000, 64, 1, 1, 1)
expect(_bytes_err(smf_extract_executable_stub(a))).to_equal("SMF_ERR_MISSING_ELF")
```

</details>

### smf arch gate (per-arch extraction)

#### an x86_64 stub requested as arm64 -> SMF_ERR_WRONG_ARCH

- an x86_64 stub requested as arm64 -> SMF_ERR_WRONG_ARCH
   - Expected: _bytes_err(smf_extract_executable_stub_for_arch(a, Architecture.Arm64)) equals `SMF_ERR_WRONG_ARCH`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an x86_64 stub requested as arm64 -> SMF_ERR_WRONG_ARCH")
val a = _smf_exe(64, 1, 1, 1)   # arch byte 1 == x86_64
expect(_bytes_err(smf_extract_executable_stub_for_arch(a, Architecture.Arm64))).to_equal("SMF_ERR_WRONG_ARCH")
```

</details>

#### an arch-unspecified (0) stub is accepted for any arch

- an arch-unspecified (0) stub is accepted for any arch
   - Expected: _bytes_err(smf_extract_executable_stub_for_arch(a, Architecture.Arm64)) equals `OK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an arch-unspecified (0) stub is accepted for any arch")
val a = _smf_exe(64, 1, 0, 1)   # arch byte 0 == unspecified
expect(_bytes_err(smf_extract_executable_stub_for_arch(a, Architecture.Arm64))).to_equal("OK")
```

</details>

### smf library extraction: role gate

#### an executable envelope requested as a library -> SMF_ERR_WRONG_ROLE

- an executable envelope requested as a library -> SMF_ERR_WRONG_ROLE
   - Expected: _bytes_err(smf_extract_library_stub(_smf_exe(64, 1, 1, 1))) equals `SMF_ERR_WRONG_ROLE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an executable envelope requested as a library -> SMF_ERR_WRONG_ROLE")
expect(_bytes_err(smf_extract_library_stub(_smf_exe(64, 1, 1, 1)))).to_equal("SMF_ERR_WRONG_ROLE")
```

</details>

### smf entry-point extraction

#### a wrong-arch entry-point request fails closed

- a wrong-arch entry-point request fails closed
   - Expected: _i64_err(smf_executable_entry_point_for_arch(a, Architecture.Arm64)) equals `SMF_ERR_WRONG_ARCH`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a wrong-arch entry-point request fails closed")
val a = _smf_exe(64, 1, 1, 1)
expect(_i64_err(smf_executable_entry_point_for_arch(a, Architecture.Arm64))).to_equal("SMF_ERR_WRONG_ARCH")
```

</details>

#### a valid envelope yields its declared entry point (positive control)

- a valid envelope yields its declared entry point (positive control)
   - Expected: _i64_ok(smf_executable_entry_point_for_arch(a, Architecture.X86_64)) equals `4096i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a valid envelope yields its declared entry point (positive control)")
val a = _smf_exe(64, 1, 1, 1)
expect(_i64_ok(smf_executable_entry_point_for_arch(a, Architecture.X86_64))).to_equal(4096i64)
```

</details>

### smf positive control: a valid envelope extracts cleanly

#### a well-formed x86_64 executable envelope returns its 64-byte ELF stub

- a well-formed x86_64 executable envelope returns its 64-byte ELF stub
   - Expected: _bytes_ok_len(smf_extract_executable_stub(a)) equals `64i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a well-formed x86_64 executable envelope returns its 64-byte ELF stub")
val a = _smf_exe(64, 1, 1, 1)
assert_true(smf_has_header(a))
expect(_bytes_ok_len(smf_extract_executable_stub(a))).to_equal(64i64)
```

</details>

### smf explicit artifact admission validates the embedded executable

#### rejects a canonical envelope whose ELF is only a matching header

- rejects a canonical envelope whose ELF is only a matching header
   - Expected: result.is_err() is true
   - Expected: result.unwrap_err() equals `SMF_ERR_MISSING_ELF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a canonical envelope whose ELF is only a matching header")
val result = smf_admit_explicit_simpleos_executable(_canonical_fake_elf_smf())
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err()).to_equal("SMF_ERR_MISSING_ELF")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
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

- Canonical SPipe generation for source `2699b87e9c88d84ed791d641aab82c47806e18d179d2c5c5554f79449759cf21`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2699b87e9c88d84ed791d641aab82c47806e18d179d2c5c5554f79449759cf21`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2699b87e9c88d84ed791d641aab82c47806e18d179d2c5c5554f79449759cf21`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/kernel/loader/smf_loader_hardening_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/loader/smf_loader_hardening_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/loader/smf_loader_hardening_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/loader/smf_loader_hardening_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/loader/smf_loader_hardening_spec.spl:109:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'an all-zero 128-byte blob has no SMF magic or header' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/loader/smf_loader_hardening_spec.spl:118:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a bare ELF file is not mistaken for an SMF envelope' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/loader/smf_loader_hardening_spec.spl:124:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a tiny (<4 byte) blob is rejected, not OOB' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
