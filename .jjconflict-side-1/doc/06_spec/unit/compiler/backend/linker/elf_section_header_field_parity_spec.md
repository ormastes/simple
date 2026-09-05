# Elf Section Header Field Parity Specification

> Tests covering every ELF64 section-header field survives BOTH readers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Elf Section Header Field Parity Specification

## Scenarios

### every ELF64 section-header field survives BOTH readers

#### elf_inspect's reader matches an independent raw byte read, per section

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- elf_inspect's reader matches an independent raw byte read, per section


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("elf_inspect's reader matches an independent raw byte read, per section")
val bytes = build_fixture()
val header = elf_parse_header(bytes).unwrap()
val secs = elf_parse_sections(bytes, header)
assert_equal(secs.len(), NSEC)

var checked: i64 = 0
var nonzero_info: i64 = 0
var i: i64 = 0
while i < NSEC:
    val base = SHOFF + i * ELF64_SHDR_SIZE
    assert_equal(secs[i].sh_name,  raw_le(bytes, base + 0, 4))
    assert_equal(secs[i].sh_type,  raw_le(bytes, base + 4, 4))
    assert_equal(secs[i].sh_flags, raw_le(bytes, base + 8, 8))
    assert_equal(secs[i].sh_size,  raw_le(bytes, base + 32, 8))
    assert_equal(secs[i].sh_info,  raw_le(bytes, base + 44, 4))
    if secs[i].sh_info != 0:
        nonzero_info = nonzero_info + 1
    checked = checked + 1
    i = i + 1

# Non-vacuity: the loop really ran, and really exercised distinct
# sh_info values rather than comparing 0 against 0 six times.
assert_equal(checked, NSEC)
assert_equal(nonzero_info, 3)
```

</details>

#### elf_parser's reader matches the same independent raw byte read

- elf_parser's reader matches the same independent raw byte read


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("elf_parser's reader matches the same independent raw byte read")
val bytes = build_fixture()
val obj = elf_parse_object(bytes).unwrap()
assert_equal(obj.sections.len(), NSEC)

var checked: i64 = 0
var nonzero_info: i64 = 0
var i: i64 = 0
while i < NSEC:
    val base = SHOFF + i * ELF64_SHDR_SIZE
    assert_equal(obj.sections[i].sh_name,  raw_le(bytes, base + 0, 4))
    assert_equal(obj.sections[i].sh_type,  raw_le(bytes, base + 4, 4))
    assert_equal(obj.sections[i].sh_flags, raw_le(bytes, base + 8, 8))
    assert_equal(obj.sections[i].sh_size,  raw_le(bytes, base + 32, 8))
    assert_equal(obj.sections[i].sh_info,  raw_le(bytes, base + 44, 4))
    # elf_parser deliberately repurposes sh_addr as the FILE OFFSET.
    assert_equal(obj.sections[i].sh_addr,  raw_le(bytes, base + 24, 8))
    if obj.sections[i].sh_info != 0:
        nonzero_info = nonzero_info + 1
    checked = checked + 1
    i = i + 1

assert_equal(checked, NSEC)
assert_equal(nonzero_info, 3)
```

</details>

#### attributes every merged relocation, and never to a single lumped target

- attributes every merged relocation, and never to a single lumped target


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("attributes every merged relocation, and never to a single lumped target")
val obj = elf_parse_object(build_fixture()).unwrap()
assert_equal(obj.relocations.len(), 3)

var distinct_targets: [i64] = []
for r in obj.relocations:
    # Each relocation's recorded target must be the sh_info of the RELA
    # section it actually came from — a per-entry invariant, not a count.
    assert_equal(r.target_section_idx, obj.sections[r.section_idx].sh_info)
    assert_equal(obj.sections[r.section_idx].sh_type, SHT_RELA)
    # The target must name a real section, never SHN_UNDEF/0.
    assert_true(r.target_section_idx > 0)
    assert_true(r.target_section_idx < NSEC)
    if not distinct_targets.contains(r.target_section_idx):
        distinct_targets = distinct_targets.push(r.target_section_idx)

# The whole point of the original bug: two RELA sections must NOT
# collapse into one indistinguishable target after the merge.
assert_equal(distinct_targets.len(), 2)
```

</details>

#### does not mistake a SYMTAB sh_info for a relocation target

- does not mistake a SYMTAB sh_info for a relocation target


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not mistake a SYMTAB sh_info for a relocation target")
# sh_info is overloaded in ELF: on SHT_SYMTAB it is the index of the
# first non-local symbol, not a section index. Parsing it is correct;
# treating it as a relocation target would not be. No relocation in this
# object may claim the symtab's sh_info as its own target section.
val obj = elf_parse_object(build_fixture()).unwrap()
val symtab_idx: i64 = 5
assert_equal(obj.sections[symtab_idx].sh_type, SHT_SYMTAB)
assert_equal(obj.sections[symtab_idx].sh_info, 3)

var from_symtab: i64 = 0
for r in obj.relocations:
    if r.section_idx == symtab_idx:
        from_symtab = from_symtab + 1
assert_equal(from_symtab, 0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/backend/linker/elf_section_header_field_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering every ELF64 section-header field survives BOTH readers.
- every ELF64 section-header field survives BOTH readers

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

- Canonical SPipe generation for source `dfaff1d96440be088529fa0a415310600c97d5e8b39650f95fc9a33801f0f233`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dfaff1d96440be088529fa0a415310600c97d5e8b39650f95fc9a33801f0f233`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dfaff1d96440be088529fa0a415310600c97d5e8b39650f95fc9a33801f0f233`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/backend/linker/elf_section_header_field_parity_spec.spl
mirror: doc/06_spec/unit/compiler/backend/linker/elf_section_header_field_parity_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/backend/linker/elf_section_header_field_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/backend/linker/elf_section_header_field_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/backend/linker/elf_section_header_field_parity_spec.spl:149:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'elf_inspect's reader matches an independent raw byte read, per section' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/linker/elf_section_header_field_parity_spec.spl:177:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'elf_parser's reader matches the same independent raw byte read' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/linker/elf_section_header_field_parity_spec.spl:204:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'attributes every merged relocation, and never to a single lumped target' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
