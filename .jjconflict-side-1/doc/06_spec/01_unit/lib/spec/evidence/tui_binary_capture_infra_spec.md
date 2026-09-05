# Tui Binary Capture Infra Specification

> Tests covering TUI screen capture and compare, Binary protocol test infra.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tui Binary Capture Infra Specification

## Scenarios

### TUI screen capture and compare

#### captures a terminal screen as a cell grid, not a lossy string blob

- captures a terminal screen as a cell grid, not a lossy string blob
- Capture a 3-row, 12-column TUI frame the way the runner records one
- Confirm the snapshot is structurally valid — cell count matches geometry
   - Expected: snapshot.rows equals `3`
   - Expected: snapshot.columns equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("captures a terminal screen as a cell grid, not a lossy string blob")
step("Capture a 3-row, 12-column TUI frame the way the runner records one")
val rows = ["File  Edit  ", "> item one  ", "  item two  "]
val snapshot = terminal_snapshot_from_rows(rows, 12)

step("Confirm the snapshot is structurally valid — cell count matches geometry")
expect(terminal_snapshot_is_valid(snapshot)).to_be(true)
expect(snapshot.rows).to_equal(3)
expect(snapshot.columns).to_equal(12)
```

</details>

#### rejects a capture with degenerate geometry instead of comparing garbage

- rejects a capture with degenerate geometry instead of comparing garbage
- Build a snapshot and break its geometry to zero columns
- Confirm validity checking refuses it
- Confirm a blanked width profile is refused too


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a capture with degenerate geometry instead of comparing garbage")
# Fail-closed at the shape the validator ACTUALLY promises: nonpositive
# geometry or a missing width profile fails. (Cell-count-vs-geometry
# cross-checking is NOT part of terminal_snapshot_is_valid today — an
# honest scope note, not a covered claim.)
step("Build a snapshot and break its geometry to zero columns")
val snapshot = terminal_snapshot_from_rows(["ab"], 12)
var broken = snapshot
broken.columns = 0

step("Confirm validity checking refuses it")
expect(terminal_snapshot_is_valid(broken)).to_be(false)

step("Confirm a blanked width profile is refused too")
var no_profile = snapshot
no_profile.width_profile = ""
expect(terminal_snapshot_is_valid(no_profile)).to_be(false)
```

</details>

#### compares a named screen region through the shared oracle model

- compares a named screen region through the shared oracle model
- Select the menu-bar region and assert its expected content
- Confirm the region selector kept its TUI identity and both checks travelled
   - Expected: selector_kind_name(menu_bar.kind) equals `terminal_region`
   - Expected: spec.checks.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("compares a named screen region through the shared oracle model")
step("Select the menu-bar region and assert its expected content")
val menu_bar = selector_terminal_region("screen#menu_bar")
val checks = [
    check_exact_selector(menu_bar, "File  Edit  "),
    check_ignore("screen#clock", "wall-clock cell differs on every capture")
]
val spec = oracle_spec("tui.screen.v1", checks)

step("Confirm the region selector kept its TUI identity and both checks travelled")
expect(selector_kind_name(menu_bar.kind)).to_equal("terminal_region")
expect(spec.checks.len()).to_equal(2)
```

</details>

### Binary protocol test infra

#### declares a protocol frame as named bit fields with a validated layout

- declares a protocol frame as named bit fields with a validated layout
- Describe a header: 4-bit version, 12-bit length, 16 reserved bits
- Confirm the layout validates — full coverage, no overlap


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("declares a protocol frame as named bit fields with a validated layout")
step("Describe a header: 4-bit version, 12-bit length, 16 reserved bits")
val layout = BinaryLayout(
    layout_id: "frame.header.v1",
    total_bits: 32,
    byte_order: ByteOrder.little,
    bit_order: BitOrder.lsb0,
    fields: [
        binary_field("version", 0, 4, "protocol version"),
        binary_field("length", 4, 12, "payload length in bytes"),
        reserved_field("reserved", 16, 16)
    ],
    source_ref: "test/01_unit/lib/spec/evidence/tui_binary_capture_infra_spec.spl"
)

step("Confirm the layout validates — full coverage, no overlap")
expect(layout_is_valid(layout)).to_be(true)
```

</details>

#### rejects an overlapping field layout instead of checking through it

- rejects an overlapping field layout instead of checking through it
- Describe a layout whose two fields claim the same bits
- Confirm validation fails and names the defect


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects an overlapping field layout instead of checking through it")
step("Describe a layout whose two fields claim the same bits")
val layout = BinaryLayout(
    layout_id: "frame.broken.v1",
    total_bits: 16,
    byte_order: ByteOrder.little,
    bit_order: BitOrder.unspecified,
    fields: [
        binary_field("a", 0, 12, "first"),
        binary_field("b", 8, 8, "overlaps a")
    ],
    source_ref: "test/01_unit/lib/spec/evidence/tui_binary_capture_infra_spec.spl"
)

step("Confirm validation fails and names the defect")
expect(layout_is_valid(layout)).to_be(false)
expect(layout_errors(layout).len()).to_be_greater_than(0)
```

</details>

#### checks one protocol field through the shared oracle model

- checks one protocol field through the shared oracle model
- Select bits 4..15 of the frame as the length field and assert it
- Confirm the selector carries its bit geometry, not just a name
   - Expected: selector_kind_name(length_field.kind) equals `binary_field`
   - Expected: length_field.start equals `4`
   - Expected: length_field.length equals `12`
   - Expected: spec.checks.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("checks one protocol field through the shared oracle model")
step("Select bits 4..15 of the frame as the length field and assert it")
val length_field = selector_binary_field("frame.header", 4, 12)
val spec = oracle_spec("frame.header.v1", [
    check_exact_selector(length_field, "512")
])

step("Confirm the selector carries its bit geometry, not just a name")
expect(selector_kind_name(length_field.kind)).to_equal("binary_field")
expect(length_field.start).to_equal(4)
expect(length_field.length).to_equal(12)
expect(spec.checks.len()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/spec/evidence/tui_binary_capture_infra_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering TUI screen capture and compare, Binary protocol test infra.
- TUI screen capture and compare
- Binary protocol test infra

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `7bd3a44c214cf40b44cece2d5846fa6b42b2fe5ca01cf670a271e8e70358affc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7bd3a44c214cf40b44cece2d5846fa6b42b2fe5ca01cf670a271e8e70358affc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7bd3a44c214cf40b44cece2d5846fa6b42b2fe5ca01cf670a271e8e70358affc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/spec/evidence/tui_binary_capture_infra_spec.spl
mirror: doc/06_spec/01_unit/lib/spec/evidence/tui_binary_capture_infra_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/spec/evidence/tui_binary_capture_infra_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/spec/evidence/tui_binary_capture_infra_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/spec/evidence/tui_binary_capture_infra_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/spec/evidence/tui_binary_capture_infra_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'captures a terminal screen as a cell grid, not a lossy string blob' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/spec/evidence/tui_binary_capture_infra_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a capture with degenerate geometry instead of comparing garbage' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/spec/evidence/tui_binary_capture_infra_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compares a named screen region through the shared oracle model' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
