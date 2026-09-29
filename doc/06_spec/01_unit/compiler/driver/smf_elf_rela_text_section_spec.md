# smf_elf_rela_text_section_spec

> Relocations embedded in an SMF module must belong to the code section(s)

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# smf_elf_rela_text_section_spec

Relocations embedded in an SMF module must belong to the code section(s)

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/smf_elf_rela_text_section_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Relocations embedded in an SMF module must belong to the code section(s)
that were actually extracted.

`extract_code_from_object` returns the concatenated bytes of every `.text*`
PROGBITS section, in section-index order; `extract_elf_relocations` returns
the entries that `build_smf_with_relocations` then applies to exactly those
bytes at load time, each one rebased to its section's offset in the merged
blob. Relocation offsets are section-relative, so the two must always agree
on which sections exist and where each one lands in the merged blob. ELF
already records the reloc-to-section link explicitly: a SHT_RELA section's
`sh_info` holds the index of the section it relocates.

These synthetic ELF64 objects probe the pairing from both sides:
 * `.rela.rodata` listed ahead of `.rela.text`
 * `-ffunction-sections` layout where `.rela.text.b` is listed ahead of
   `.rela.text.a` -- both `.text.a` and `.text.b` must be extracted (not just
   the first), and each section's relocations must be rebased to its own
   offset in the merged Code blob
 * a truncated object file, to prove `extract_code_from_object` and
   `extract_elf_relocations` still agree on which sections exist (neither
   accepts a `.text` section whose bytes run past the end of the buffer)

## Scenarios

### SMF ELF relocation extraction

#### returns exactly one entry for an object with a decoy .rela.rodata

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns exactly one entry for an object with a decoy .rela.rodata


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns exactly one entry for an object with a decoy .rela.rodata")
val relocs = extract_elf_relocations(build_object_with_rodata_relocs_first())
assert_equal(relocs.len(), 1)
```

</details>

#### returns the .rela.text offset, not that of an earlier .rela.* section

- returns the .rela.text offset, not that of an earlier .rela.* section


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns the .rela.text offset, not that of an earlier .rela.* section")
val relocs = extract_elf_relocations(build_object_with_rodata_relocs_first())
assert_equal(relocs[0].offset, 0xBBBB)
```

</details>

#### returns the .rela.text symbol index and type

- returns the .rela.text symbol index and type


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns the .rela.text symbol index and type")
val relocs = extract_elf_relocations(build_object_with_rodata_relocs_first())
assert_equal(relocs[0].sym_idx, 1)
assert_equal(relocs[0].reloc_type, 2)
```

</details>

#### returns the .rela.text addend

- returns the .rela.text addend


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns the .rela.text addend")
val relocs = extract_elf_relocations(build_object_with_rodata_relocs_first())
assert_equal(relocs[0].addend, 7)
```

</details>

### SMF ELF relocations pair with the extracted code section

#### concatenates BOTH .text.a and .text.b under a -ffunction-sections layout (no silent code drop)

- concatenates BOTH .text.a and .text.b under a -ffunction-sections layout (no silent code drop)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("concatenates BOTH .text.a and .text.b under a -ffunction-sections layout (no silent code drop)")
val code = extract_code_from_object(build_function_sections_object())
assert_equal(code.len(), 8)
assert_equal(code[1] as i64, 1)   # byte 1 of .text.a's 4 bytes
assert_equal(code[5] as i64, 2)   # byte 1 of .text.b's 4 bytes, at merged offset 4
```

</details>

#### returns relocations for BOTH sections, each rebased to its offset in the merged blob

- returns relocations for BOTH sections, each rebased to its offset in the merged blob


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns relocations for BOTH sections, each rebased to its offset in the merged blob")
val relocs = extract_elf_relocations(build_function_sections_object())
assert_equal(relocs.len(), 2)
# .text.a is first in the merged blob (base 0): .rela.text.a's r_offset unchanged.
assert_equal(relocs[0].offset, 0xDDDD)
assert_equal(relocs[0].sym_idx, 1)
assert_equal(relocs[0].addend, 7)
# .text.b starts at offset 4 in the merged blob (after .text.a's 4 bytes):
# .rela.text.b's r_offset 0xCCCC must be rebased by +4.
assert_equal(relocs[1].offset, 0xCCCC + 4)
```

</details>

### SMF ELF text-section discovery agrees on truncated objects

#### extract_code_from_object and extract_elf_relocations both skip a .text section truncated past EOF

- extract_code_from_object and extract_elf_relocations both skip a .text section truncated past EOF


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extract_code_from_object and extract_elf_relocations both skip a .text section truncated past EOF")
# Same layout as build_object_with_rodata_relocs_first(), but the
# buffer is cut off before .text's declared [offset, offset+size)
# range ends -- object_code.len() < sec_offset + sec_size for the
# ".text" section (offset 352, size 4, but buffer ends at 353).
val full = build_object_with_rodata_relocs_first()
val truncated = truncate_to(full, 353)
val code = extract_code_from_object(truncated)
# No section header names a valid, fully in-bounds ".text" section,
# so this must fall back to raw bytes -- NOT the 3 in-bounds bytes of
# the declared-but-truncated .text section. If this ever returns a
# partial 3-byte slice instead, extract_code_from_object started
# accepting a section _find_text_section_index() would reject as
# out-of-bounds, and the sibling-agreement guard regressed.
assert_equal(code.len(), truncated.len())
val relocs = extract_elf_relocations(truncated)
assert_equal(relocs.len(), 0)
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `07543adc372fee3044582e34f02cbb8fa38785f0648ca1fd8fa5818759e4a18d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `07543adc372fee3044582e34f02cbb8fa38785f0648ca1fd8fa5818759e4a18d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `07543adc372fee3044582e34f02cbb8fa38785f0648ca1fd8fa5818759e4a18d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/driver/smf_elf_rela_text_section_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/smf_elf_rela_text_section_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/driver/smf_elf_rela_text_section_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/smf_elf_rela_text_section_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/smf_elf_rela_text_section_spec.spl:159:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns exactly one entry for an object with a decoy .rela.rodata' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/smf_elf_rela_text_section_spec.spl:165:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the .rela.text offset, not that of an earlier .rela.* section' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/smf_elf_rela_text_section_spec.spl:171:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the .rela.text symbol index and type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
