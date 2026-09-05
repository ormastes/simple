# T32 Cli Catalog Specification

> Tests covering T32 Catalog Loader (real SDN files).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 Cli Catalog Specification

## Scenarios

### T32 Catalog Loader (real SDN files)

#### windows.sdn

#### loads window entries from real catalog file

- loads window entries from real catalog file


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("loads window entries from real catalog file")
val content = rt_file_read_text("config/t32/catalogs/windows.sdn") ?? ""
val entries = sdn_parse_block(content, "window")
expect(entries.len()).to_be_greater_than(0)
```

</details>

#### has at least 11 windows

- has at least 11 windows


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has at least 11 windows")
val content = rt_file_read_text("config/t32/catalogs/windows.sdn") ?? ""
val entries = sdn_parse_block(content, "window")
expect(entries.len()).to_be_greater_than(10)
```

</details>

#### contains break_list window

- contains break_list window
   - Expected: e["title"] ?? "" equals `Breakpoint List`
   - Expected: e["kind"] ?? "" equals `built_in`
   - Expected: found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains break_list window")
val content = rt_file_read_text("config/t32/catalogs/windows.sdn") ?? ""
val entries = sdn_parse_block(content, "window")
var found = false
for e in entries:
    val key = e["_key"] ?? ""
    if key == "break_list":
        found = true
        expect(e["title"] ?? "").to_equal("Breakpoint List")
        expect(e["kind"] ?? "").to_equal("built_in")
expect(found).to_equal(true)
```

</details>

#### contains register_view window

- contains register_view window
   - Expected: e["title"] ?? "" equals `CPU Registers`
   - Expected: found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains register_view window")
val content = rt_file_read_text("config/t32/catalogs/windows.sdn") ?? ""
val entries = sdn_parse_block(content, "window")
var found = false
for e in entries:
    val key = e["_key"] ?? ""
    if key == "register_view":
        found = true
        expect(e["title"] ?? "").to_equal("CPU Registers")
expect(found).to_equal(true)
```

</details>

#### each window has open_command

- each window has open_command


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("each window has open_command")
val content = rt_file_read_text("config/t32/catalogs/windows.sdn") ?? ""
val entries = sdn_parse_block(content, "window")
for e in entries:
    val open_cmd = e["open_command"] ?? ""
    expect(open_cmd.len()).to_be_greater_than(0)
```

</details>

#### actions.sdn

#### loads action entries from real catalog file

- loads action entries from real catalog file


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("loads action entries from real catalog file")
val content = rt_file_read_text("config/t32/catalogs/actions.sdn") ?? ""
val entries = sdn_parse_block(content, "action")
expect(entries.len()).to_be_greater_than(0)
```

</details>

#### has at least 10 actions

- has at least 10 actions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has at least 10 actions")
val content = rt_file_read_text("config/t32/catalogs/actions.sdn") ?? ""
val entries = sdn_parse_block(content, "action")
expect(entries.len()).to_be_greater_than(9)
```

</details>

#### contains set_break action with correct fields

- contains set_break action with correct fields
   - Expected: e["label"] ?? "" equals `Set Breakpoint`
   - Expected: e["type"] ?? "" equals `execute`
   - Expected: found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains set_break action with correct fields")
val content = rt_file_read_text("config/t32/catalogs/actions.sdn") ?? ""
val entries = sdn_parse_block(content, "action")
var found = false
for e in entries:
    val key = e["_key"] ?? ""
    if key == "set_break":
        found = true
        expect(e["label"] ?? "").to_equal("Set Breakpoint")
        expect(e["type"] ?? "").to_equal("execute")
expect(found).to_equal(true)
```

</details>

#### fields.sdn

#### loads field entries from real catalog file

- loads field entries from real catalog file


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("loads field entries from real catalog file")
val content = rt_file_read_text("config/t32/catalogs/fields.sdn") ?? ""
val entries = sdn_parse_block(content, "field")
expect(entries.len()).to_be_greater_than(0)
```

</details>

#### has at least 10 fields

- has at least 10 fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has at least 10 fields")
val content = rt_file_read_text("config/t32/catalogs/fields.sdn") ?? ""
val entries = sdn_parse_block(content, "field")
expect(entries.len()).to_be_greater_than(9)
```

</details>

#### contains symbol field with correct properties

- contains symbol field with correct properties
   - Expected: e["label"] ?? "" equals `Symbol Name`
   - Expected: e["type"] ?? "" equals `string`
   - Expected: e["scope"] ?? "" equals `window`
   - Expected: found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains symbol field with correct properties")
val content = rt_file_read_text("config/t32/catalogs/fields.sdn") ?? ""
val entries = sdn_parse_block(content, "field")
var found = false
for e in entries:
    val key = e["_key"] ?? ""
    if key == "symbol":
        found = true
        expect(e["label"] ?? "").to_equal("Symbol Name")
        expect(e["type"] ?? "").to_equal("string")
        expect(e["scope"] ?? "").to_equal("window")
expect(found).to_equal(true)
```

</details>

#### lookup by key

#### finds window by key

- finds window by key
   - Expected: found_title equals `Trace List`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds window by key")
val content = rt_file_read_text("config/t32/catalogs/windows.sdn") ?? ""
val entries = sdn_parse_block(content, "window")
var found_title = ""
for e in entries:
    if (e["_key"] ?? "") == "trace_list":
        found_title = e["title"] ?? ""
expect(found_title).to_equal("Trace List")
```

</details>

#### finds action by key

- finds action by key
   - Expected: found_label equals `Resume Execution`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds action by key")
val content = rt_file_read_text("config/t32/catalogs/actions.sdn") ?? ""
val entries = sdn_parse_block(content, "action")
var found_label = ""
for e in entries:
    if (e["_key"] ?? "") == "go":
        found_label = e["label"] ?? ""
expect(found_label).to_equal("Resume Execution")
```

</details>

#### finds field by key

- finds field by key
   - Expected: found_label equals `ELF Binary Path`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds field by key")
val content = rt_file_read_text("config/t32/catalogs/fields.sdn") ?? ""
val entries = sdn_parse_block(content, "field")
var found_label = ""
for e in entries:
    if (e["_key"] ?? "") == "elf_path":
        found_label = e["label"] ?? ""
expect(found_label).to_equal("ELF Binary Path")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/t32_cli/t32_cli_catalog_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering T32 Catalog Loader (real SDN files).
- T32 Catalog Loader (real SDN files)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
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

- Canonical SPipe generation for source `0b5711e53733e29339449d71c3d5b60d71750dbd143f4db1d31dfd4109235af7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0b5711e53733e29339449d71c3d5b60d71750dbd143f4db1d31dfd4109235af7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0b5711e53733e29339449d71c3d5b60d71750dbd143f4db1d31dfd4109235af7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/t32_cli/t32_cli_catalog_spec.spl
mirror: doc/06_spec/unit/app/t32_cli/t32_cli_catalog_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/t32_cli/t32_cli_catalog_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/t32_cli/t32_cli_catalog_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/t32_cli/t32_cli_catalog_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'loads window entries from real catalog file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/t32_cli/t32_cli_catalog_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has at least 11 windows' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/t32_cli/t32_cli_catalog_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'contains break_list window' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
