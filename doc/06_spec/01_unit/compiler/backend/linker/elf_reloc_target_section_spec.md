# Elf Reloc Target Section Specification

> Tests covering ELF relocations keep their target section across the merge.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Elf Reloc Target Section Specification

## Scenarios

### ELF relocations keep their target section across the merge

#### parses the fixture object at all

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses the fixture object at all


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses the fixture object at all")
val obj_r = elf_parse_object(build_two_rela_object())
assert_true(obj_r.is_ok())
val obj = obj_r.unwrap()
assert_equal(obj.sections.len(), 5)
# Guard against a vacuous run: the merged list must be non-empty.
assert_equal(obj.relocations.len(), 3)
```

</details>

#### records sh_info on each RELA section header

- records sh_info on each RELA section header


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records sh_info on each RELA section header")
val obj = elf_parse_object(build_two_rela_object()).unwrap()
assert_equal(obj.sections[RELA_TEXT_IDX].sh_info, TEXT_IDX)
assert_equal(obj.sections[RELA_DATA_IDX].sh_info, DATA_IDX)
# A non-RELA section's sh_info is 0 here, so a hardcoded constant
# cannot satisfy both assertions above and this one.
assert_equal(obj.sections[TEXT_IDX].sh_info, 0)
```

</details>

#### attributes every merged relocation to the section it applies to

- attributes every merged relocation to the section it applies to


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("attributes every merged relocation to the section it applies to")
val obj = elf_parse_object(build_two_rela_object()).unwrap()

var to_text: i64 = 0
var to_data: i64 = 0
var unattributed: i64 = 0
for r in obj.relocations:
    if r.target_section_idx == TEXT_IDX:
        to_text = to_text + 1
    else:
        if r.target_section_idx == DATA_IDX:
            to_data = to_data + 1
        else:
            unattributed = unattributed + 1

# This is the assertion that was impossible before the fix: with sh_info
# unparsed every relocation reported target 0 and unattributed == 3.
assert_equal(unattributed, 0)
assert_equal(to_text, 2)
assert_equal(to_data, 1)
```

</details>

#### keeps target_section_idx consistent with the owning RELA header

- keeps target_section_idx consistent with the owning RELA header


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps target_section_idx consistent with the owning RELA header")
val obj = elf_parse_object(build_two_rela_object()).unwrap()
var checked: i64 = 0
for r in obj.relocations:
    assert_equal(r.target_section_idx, obj.sections[r.section_idx].sh_info)
    checked = checked + 1
assert_equal(checked, 3)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/linker/elf_reloc_target_section_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ELF relocations keep their target section across the merge.
- ELF relocations keep their target section across the merge

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

- Canonical SPipe generation for source `a1928b0fb1c863efc7baef5b42ab6443b94cedd58482230c82795eb849bcf19f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a1928b0fb1c863efc7baef5b42ab6443b94cedd58482230c82795eb849bcf19f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a1928b0fb1c863efc7baef5b42ab6443b94cedd58482230c82795eb849bcf19f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/backend/linker/elf_reloc_target_section_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/linker/elf_reloc_target_section_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/linker/elf_reloc_target_section_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/linker/elf_reloc_target_section_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/linker/elf_reloc_target_section_spec.spl:137:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses the fixture object at all' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/linker/elf_reloc_target_section_spec.spl:147:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records sh_info on each RELA section header' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/linker/elf_reloc_target_section_spec.spl:157:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'attributes every merged relocation to the section it applies to' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
