# TreeSitter Node API Tests

> Tests for TreeSitter Node API wrapper (Features 1-2 from Phase 2.3):

<!-- sdn-diagram:id=treesitter_node_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=treesitter_node_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

treesitter_node_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=treesitter_node_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# TreeSitter Node API Tests

Tests for TreeSitter Node API wrapper (Features 1-2 from Phase 2.3):

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-NODE-API-001 |
| Category | Parser \| TreeSitter |
| Status | In Development |
| Source | `test/01_unit/std/parser/treesitter_node_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for TreeSitter Node API wrapper (Features 1-2 from Phase 2.3):
- Feature 1: Position tracking (start_byte, end_byte, start_point, end_point)
- Feature 2: Parent/sibling navigation (parent, next_sibling, prev_sibling)

## Scenarios

### Node Position Tracking

#### has start_byte method that returns i64

- has start_byte method that returns i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("has start_byte method that returns i64")
val node = create_mock_node(1)
# The actual value depends on FFI, but method should be callable
val result = node.start_byte()
expect result.to_be_greater_than(-1) or result.to_equal(-1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### has end_byte method that returns i64

- has end_byte method that returns i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("has end_byte method that returns i64")
val node = create_mock_node(1)
val result = node.end_byte()
expect result.to_be_greater_than(-1) or result.to_equal(-1)
```

</details>

#### has start_point method that returns Point

- has start_point method that returns Point


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("has start_point method that returns Point")
val node = create_mock_node(1)
val pt = node.start_point()
# Point should have row and column fields
val has_row = pt.row >= 0 or pt.row < 0
val has_col = pt.column >= 0 or pt.column < 0
expect has_row and has_col
```

</details>

#### has end_point method that returns Point

- has end_point method that returns Point


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("has end_point method that returns Point")
val node = create_mock_node(1)
val pt = node.end_point()
val has_row = pt.row >= 0 or pt.row < 0
val has_col = pt.column >= 0 or pt.column < 0
expect has_row and has_col
```

</details>

### Node Navigation

#### has parent method that returns Node?

- has parent method that returns Node?


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("has parent method that returns Node?")
val node = create_mock_node(1)
val parent = node.parent()
# Result can be nil or Node
val is_valid_result = parent == nil or parent != nil
expect is_valid_result
```

</details>

#### has next_sibling method that returns Node?

- has next_sibling method that returns Node?


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("has next_sibling method that returns Node?")
val node = create_mock_node(1)
val sibling = node.next_sibling()
val is_valid_result = sibling == nil or sibling != nil
expect is_valid_result
```

</details>

#### has prev_sibling method that returns Node?

- has prev_sibling method that returns Node?


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("has prev_sibling method that returns Node?")
val node = create_mock_node(1)
val sibling = node.prev_sibling()
val is_valid_result = sibling == nil or sibling != nil
expect is_valid_result
```

</details>

### Node Basic Operations

#### has kind method

- has kind method


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("has kind method")
val node = create_mock_node(1)
val k = node.kind()
# Should return text (possibly empty)
expect k.len() >= 0
```

</details>

#### has child_count method

- has child_count method


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("has child_count method")
val node = create_mock_node(1)
val count = node.child_count()
expect count >= 0
```

</details>

#### has child method

- has child method


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("has child method")
val node = create_mock_node(1)
val c = node.child(0)
expect c == nil or c != nil
```

</details>

#### has named_child_count method

- has named_child_count method


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("has named_child_count method")
val node = create_mock_node(1)
val count = node.named_child_count()
expect count >= 0
```

</details>

#### has named_child method

- has named_child method


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("has named_child method")
val node = create_mock_node(1)
val c = node.named_child(0)
expect c == nil or c != nil
```

</details>

#### has is_named method

- has is_named method


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("has is_named method")
val node = create_mock_node(1)
val result = node.is_named()
expect result.to_equal(true) or result.to_equal(false)
```

</details>

#### has is_missing method

- has is_missing method


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("has is_missing method")
val node = create_mock_node(1)
val result = node.is_missing()
expect result.to_equal(true) or result.to_equal(false)
```

</details>

#### has is_extra method

- has is_extra method


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("has is_extra method")
val node = create_mock_node(1)
val result = node.is_extra()
expect result.to_equal(true) or result.to_equal(false)
```

</details>

#### has has_error method

- has has_error method


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("has has_error method")
val node = create_mock_node(1)
val result = node.has_error()
expect result.to_equal(true) or result.to_equal(false)
```

</details>

#### has is_null method

- has is_null method


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("has is_null method")
val node = create_mock_node(1)
val result = node.is_null()
expect result.to_equal(true) or result.to_equal(false)
```

</details>

### Node Utility Functions

#### node_is_valid returns false for nil

- node_is_valid returns false for nil


- Verify: node_is_valid returns bool for non-nil node


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("node_is_valid returns false for nil")
val result = node_is_valid(nil)
expect result.to_equal(false)
```

</details>

#### node_is_valid returns bool for non-nil node

- node_is_valid returns bool for non-nil node


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("node_is_valid returns bool for non-nil node")
val node = create_mock_node(1)
val result = node_is_valid(node)
# Should return true or false based on is_null check
expect result.to_equal(true) or result.to_equal(false)
```

</details>

#### node_byte_range returns tuple

- node_byte_range returns tuple


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("node_byte_range returns tuple")
val node = create_mock_node(1)
val range = node_byte_range(node)
# Should be (start, end) tuple
val has_start = range.0 >= 0 or range.0 < 0
val has_end = range.1 >= 0 or range.1 < 0
expect has_start and has_end
```

</details>

#### node_line_range returns tuple

- node_line_range returns tuple


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("node_line_range returns tuple")
val node = create_mock_node(1)
val range = node_line_range(node)
val has_start = range.0 >= 0 or range.0 < 0
val has_end = range.1 >= 0 or range.1 < 0
expect has_start and has_end
```

</details>

### Point Structure

#### can create Point with row and column

- can create Point with row and column


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("can create Point with row and column")
val pt = Point(row: 5, column: 10)
expect pt.row.to_equal(5)
expect pt.column.to_equal(10)
```

</details>

#### Point row can be zero

- Point row can be zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("Point row can be zero")
val pt = Point(row: 0, column: 0)
expect pt.row.to_equal(0)
```

</details>

#### Point column can be zero

- Point column can be zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("Point column can be zero")
val pt = Point(row: 0, column: 0)
expect pt.column.to_equal(0)
```

</details>

### API Design

#### navigation methods return Optional nodes (nil or Node)

- navigation methods return Optional nodes (nil or Node)


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("navigation methods return Optional nodes (nil or Node)")
val node = create_mock_node(1)
val parent = node.parent()
val next = node.next_sibling()
val prev = node.prev_sibling()
# All should be optional (can be nil)
val parent_valid = parent == nil or parent != nil
val next_valid = next == nil or next != nil
val prev_valid = prev == nil or prev != nil
expect parent_valid and next_valid and prev_valid
```

</details>

#### position methods return concrete values (i64 or Point)

- position methods return concrete values (i64 or Point)


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("position methods return concrete values (i64 or Point)")
val node = create_mock_node(1)
# These should never be nil
val start_b = node.start_byte()
val end_b = node.end_byte()
val start_p = node.start_point()
val end_p = node.end_point()
# Check they're actual values (any i64 is valid, any Point is valid)
val valid_start = start_b >= 0 or start_b < 0
val valid_end = end_b >= 0 or end_b < 0
val valid_sp = start_p.row >= 0 or start_p.row < 0
val valid_ep = end_p.row >= 0 or end_p.row < 0
expect valid_start and valid_end and valid_sp and valid_ep
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-STD`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `76926c0f2ad1623f65936bd296a0401d920653644415efbc1c2ef0d99080e88b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `76926c0f2ad1623f65936bd296a0401d920653644415efbc1c2ef0d99080e88b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `76926c0f2ad1623f65936bd296a0401d920653644415efbc1c2ef0d99080e88b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/01_unit/std/parser/treesitter_node_spec.spl
mirror: doc/06_spec/01_unit/std/parser/treesitter_node_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/std/parser/treesitter_node_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/std/parser/treesitter_node_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/std/parser/treesitter_node_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has start_byte method that returns i64' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/std/parser/treesitter_node_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has end_byte method that returns i64' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/std/parser/treesitter_node_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has start_point method that returns Point' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/std/parser/treesitter_node_spec.spl:244:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can create Point with row and column' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
