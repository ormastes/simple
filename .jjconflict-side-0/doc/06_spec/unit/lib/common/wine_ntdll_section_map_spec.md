# Wine Ntdll Section Map Specification

> Tests covering Wine NTDLL section map bridge.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Ntdll Section Map Specification

## Scenarios

### Wine NTDLL section map bridge

#### executes a bounded NtCreateSection, NtMapViewOfSection, and NtUnmapViewOfSection sequence

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- executes a bounded NtCreateSection, NtMapViewOfSection, and NtUnmapViewOfSection sequence
   - Expected: result.ok is true
   - Expected: result.handle equals `0x400`
   - Expected: result.mapped_base equals `0x400000`
   - Expected: result.table.sections[0].mapped_base equals `0`
   - Expected: result.space.regions.len() equals `0`
   - Expected: result.operations equals `NtCreateSection NtMapViewOfSection NtUnmapViewOfSection`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes a bounded NtCreateSection, NtMapViewOfSection, and NtUnmapViewOfSection sequence")
val result = wine_ntdll_execute_section_map(
    ["NtCreateSection", "NtMapViewOfSection", "NtUnmapViewOfSection"],
    wine_ntdll_section_table_new(),
    wine_vm_process_space_new(10, 9000, "pid fs ipc net capability"),
    "\\KnownDlls\\kernel32.dll",
    0x3000,
    0x400000
)

expect(result.ok).to_equal(true)
expect(result.handle).to_equal(0x400)
expect(result.mapped_base).to_equal(0x400000)
expect(result.table.sections[0].mapped_base).to_equal(0)
expect(result.space.regions.len()).to_equal(0)
expect(result.operations).to_equal("NtCreateSection NtMapViewOfSection NtUnmapViewOfSection")
```

</details>

#### keeps NTDLL section mapping ordered and bounded

- keeps NTDLL section mapping ordered and bounded
   - Expected: out_of_order.ok is false
   - Expected: out_of_order.error equals `ntdll-section-map-sequence-expected:NtCreateSection`
   - Expected: wrong_family.ok is false
   - Expected: wrong_family.error equals `bridge-wrong-category:NtCreateFile`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps NTDLL section mapping ordered and bounded")
val out_of_order = wine_ntdll_execute_section_map(
    ["NtMapViewOfSection", "NtCreateSection", "NtUnmapViewOfSection"],
    wine_ntdll_section_table_new(),
    wine_vm_process_space_new(10, 9000, "pid fs ipc net capability"),
    "\\KnownDlls\\kernel32.dll",
    0x3000,
    0x400000
)
expect(out_of_order.ok).to_equal(false)
expect(out_of_order.error).to_equal("ntdll-section-map-sequence-expected:NtCreateSection")

val wrong_family = wine_ntdll_execute_section_map(
    ["NtCreateSection", "NtMapViewOfSection", "NtCreateFile"],
    wine_ntdll_section_table_new(),
    wine_vm_process_space_new(10, 9000, "pid fs ipc net capability"),
    "\\KnownDlls\\kernel32.dll",
    0x3000,
    0x400000
)
expect(wrong_family.ok).to_equal(false)
expect(wrong_family.error).to_equal("bridge-wrong-category:NtCreateFile")
```

</details>

#### rejects invalid section descriptors and conflicting view bases

- rejects invalid section descriptors and conflicting view bases
   - Expected: invalid.ok is false
   - Expected: invalid.error equals `NtCreateSection:invalid-name`
   - Expected: conflict.ok is false
   - Expected: conflict.error equals `NtMapViewOfSection:fixed-map-conflict`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid section descriptors and conflicting view bases")
val invalid = wine_ntdll_execute_section_map(
    ["NtCreateSection", "NtMapViewOfSection", "NtUnmapViewOfSection"],
    wine_ntdll_section_table_new(),
    wine_vm_process_space_new(10, 9000, "pid fs ipc net capability"),
    "",
    0x3000,
    0x400000
)
expect(invalid.ok).to_equal(false)
expect(invalid.error).to_equal("NtCreateSection:invalid-name")

val occupied = wine_vm_map_executable_image(wine_vm_process_space_new(10, 9000, "pid fs ipc net capability"), 0x400000, 0x1000)
val conflict = wine_ntdll_execute_section_map(
    ["NtCreateSection", "NtMapViewOfSection", "NtUnmapViewOfSection"],
    wine_ntdll_section_table_new(),
    occupied.space,
    "\\KnownDlls\\user32.dll",
    0x3000,
    0x400000
)
expect(conflict.ok).to_equal(false)
expect(conflict.error).to_equal("NtMapViewOfSection:fixed-map-conflict")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/wine_ntdll_section_map_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine NTDLL section map bridge.
- Wine NTDLL section map bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `814386e2e662c040a86fbcc9c71372a78c0d447047a153ccc34fca12716dec20`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `814386e2e662c040a86fbcc9c71372a78c0d447047a153ccc34fca12716dec20`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `814386e2e662c040a86fbcc9c71372a78c0d447047a153ccc34fca12716dec20`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/common/wine_ntdll_section_map_spec.spl
mirror: doc/06_spec/unit/lib/common/wine_ntdll_section_map_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/wine_ntdll_section_map_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/wine_ntdll_section_map_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/wine_ntdll_section_map_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/wine_ntdll_section_map_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes a bounded NtCreateSection, NtMapViewOfSection, and NtUnmapViewOfSection sequence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_ntdll_section_map_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps NTDLL section mapping ordered and bounded' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_ntdll_section_map_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects invalid section descriptors and conflicting view bases' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
