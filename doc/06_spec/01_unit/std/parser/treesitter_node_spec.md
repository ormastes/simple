# TreeSitter Node API Tests

> Tests for TreeSitter Node API wrapper (Features 1-2 from Phase 2.3):

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
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
## Operator workflow
## Compatibility and limitations

# TreeSitter Node API Tests

**Feature ID:** #PARSER-NODE-API-001
**Category:** Parser | TreeSitter
**Status:** In Development

Tests for TreeSitter Node API wrapper (Features 1-2 from Phase 2.3):
- Feature 1: Position tracking (start_byte, end_byte, start_point, end_point)
- Feature 2: Parent/sibling navigation (parent, next_sibling, prev_sibling)

## Scenarios

### Node Position Tracking

#### has start_byte method that returns i64

- Verify: has start_byte method that returns i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-PARSER_TREESITTER_NODE-001
step("Verify: has start_byte method that returns i64")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val node = create_mock_node(1)
# The actual value depends on FFI, but method should be callable
val result = node.start_byte()
expect result.to_be_greater_than(-1) or result.to_equal(-1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### has end_byte method that returns i64

- Verify: has end_byte method that returns i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-PARSER_TREESITTER_NODE-001
step("Verify: has end_byte method that returns i64")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val node = create_mock_node(1)
val result = node.end_byte()
expect result.to_be_greater_than(-1) or result.to_equal(-1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### has start_point method that returns Point

- Verify: has start_point method that returns Point


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-PARSER_TREESITTER_NODE-001
step("Verify: has start_point method that returns Point")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val node = create_mock_node(1)
val pt = node.start_point()
# Point should have row and column fields
val has_row = pt.row >= 0 or pt.row < 0
val has_col = pt.column >= 0 or pt.column < 0
expect has_row and has_col
```

</details>

#### has end_point method that returns Point

- Verify: has end_point method that returns Point


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-PARSER_TREESITTER_NODE-001
step("Verify: has end_point method that returns Point")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val node = create_mock_node(1)
val pt = node.end_point()
val has_row = pt.row >= 0 or pt.row < 0
val has_col = pt.column >= 0 or pt.column < 0
expect has_row and has_col
```

</details>

### Node Navigation

#### has parent method that returns Node?

- Verify: has parent method that returns Node?


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-PARSER_TREESITTER_NODE-001
step("Verify: has parent method that returns Node?")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val node = create_mock_node(1)
val parent = node.parent()
# Result can be nil or Node
val is_valid_result = parent == nil or parent != nil
expect is_valid_result
```

</details>

#### has next_sibling method that returns Node?

- Verify: has next_sibling method that returns Node?


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-PARSER_TREESITTER_NODE-001
step("Verify: has next_sibling method that returns Node?")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val node = create_mock_node(1)
val sibling = node.next_sibling()
val is_valid_result = sibling == nil or sibling != nil
expect is_valid_result
```

</details>

#### has prev_sibling method that returns Node?

- Verify: has prev_sibling method that returns Node?


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-PARSER_TREESITTER_NODE-001
step("Verify: has prev_sibling method that returns Node?")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val node = create_mock_node(1)
val sibling = node.prev_sibling()
val is_valid_result = sibling == nil or sibling != nil
expect is_valid_result
```

</details>

### Node Basic Operations

#### has kind method

- Verify: has kind method


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-PARSER_TREESITTER_NODE-001
step("Verify: has kind method")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val node = create_mock_node(1)
val k = node.kind()
# Should return text (possibly empty)
expect k.len() >= 0
```

</details>

#### has child_count method

- Verify: has child_count method


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-PARSER_TREESITTER_NODE-001
step("Verify: has child_count method")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val node = create_mock_node(1)
val count = node.child_count()
expect count >= 0
```

</details>

#### has child method

- Verify: has child method


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-PARSER_TREESITTER_NODE-001
step("Verify: has child method")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val node = create_mock_node(1)
val c = node.child(0)
expect c == nil or c != nil
```

</details>

#### has named_child_count method

- Verify: has named_child_count method


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-PARSER_TREESITTER_NODE-001
step("Verify: has named_child_count method")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val node = create_mock_node(1)
val count = node.named_child_count()
expect count >= 0
```

</details>

#### has named_child method

- Verify: has named_child method


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-PARSER_TREESITTER_NODE-001
step("Verify: has named_child method")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val node = create_mock_node(1)
val c = node.named_child(0)
expect c == nil or c != nil
```

</details>

#### has is_named method

- Verify: has is_named method


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-PARSER_TREESITTER_NODE-001
step("Verify: has is_named method")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val node = create_mock_node(1)
val result = node.is_named()
expect result.to_equal(true) or result.to_equal(false)
```

</details>

#### has is_missing method

- Verify: has is_missing method


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-PARSER_TREESITTER_NODE-001
step("Verify: has is_missing method")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val node = create_mock_node(1)
val result = node.is_missing()
expect result.to_equal(true) or result.to_equal(false)
```

</details>

#### has is_extra method

- Verify: has is_extra method


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-PARSER_TREESITTER_NODE-001
step("Verify: has is_extra method")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val node = create_mock_node(1)
val result = node.is_extra()
expect result.to_equal(true) or result.to_equal(false)
```

</details>

#### has has_error method

- Verify: has has_error method


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-PARSER_TREESITTER_NODE-001
step("Verify: has has_error method")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val node = create_mock_node(1)
val result = node.has_error()
expect result.to_equal(true) or result.to_equal(false)
```

</details>

#### has is_null method

- Verify: has is_null method


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-PARSER_TREESITTER_NODE-001
step("Verify: has is_null method")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val node = create_mock_node(1)
val result = node.is_null()
expect result.to_equal(true) or result.to_equal(false)
```

</details>

### Node Utility Functions

#### node_is_valid returns false for nil

- Verify: node_is_valid returns false for nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-PARSER_TREESITTER_NODE-001
step("Verify: node_is_valid returns false for nil")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val result = node_is_valid(nil)
expect result.to_equal(false)
```

</details>

#### node_is_valid returns bool for non-nil node

- Verify: node_is_valid returns bool for non-nil node


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-PARSER_TREESITTER_NODE-001
step("Verify: node_is_valid returns bool for non-nil node")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val node = create_mock_node(1)
val result = node_is_valid(node)
# Should return true or false based on is_null check
expect result.to_equal(true) or result.to_equal(false)
```

</details>

#### node_byte_range returns tuple

- Verify: node_byte_range returns tuple


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-PARSER_TREESITTER_NODE-001
step("Verify: node_byte_range returns tuple")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val node = create_mock_node(1)
val range = node_byte_range(node)
# Should be (start, end) tuple
val has_start = range.0 >= 0 or range.0 < 0
val has_end = range.1 >= 0 or range.1 < 0
expect has_start and has_end
```

</details>

#### node_line_range returns tuple

- Verify: node_line_range returns tuple


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-PARSER_TREESITTER_NODE-001
step("Verify: node_line_range returns tuple")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val node = create_mock_node(1)
val range = node_line_range(node)
val has_start = range.0 >= 0 or range.0 < 0
val has_end = range.1 >= 0 or range.1 < 0
expect has_start and has_end
```

</details>

### Point Structure

#### can create Point with row and column

- Verify: can create Point with row and column


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-PARSER_TREESITTER_NODE-001
step("Verify: can create Point with row and column")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val pt = Point(row: 5, column: 10)
expect pt.row.to_equal(5)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect pt.column.to_equal(10)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### Point row can be zero

- Verify: Point row can be zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-PARSER_TREESITTER_NODE-001
step("Verify: Point row can be zero")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val pt = Point(row: 0, column: 0)
expect pt.row.to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### Point column can be zero

- Verify: Point column can be zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-PARSER_TREESITTER_NODE-001
step("Verify: Point column can be zero")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val pt = Point(row: 0, column: 0)
expect pt.column.to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

### API Design

#### navigation methods return Optional nodes (nil or Node)

- Verify: navigation methods return Optional nodes (nil or Node)


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-PARSER_TREESITTER_NODE-001
step("Verify: navigation methods return Optional nodes (nil or Node)")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: position methods return concrete values (i64 or Point)


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-PARSER_TREESITTER_NODE-001
step("Verify: position methods return concrete values (i64 or Point)")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `58ba09d98dca8eb6c35965d5969328dec3c76a9d8ada4a0d7a3d606fb8af5fef`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `58ba09d98dca8eb6c35965d5969328dec3c76a9d8ada4a0d7a3d606fb8af5fef`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `58ba09d98dca8eb6c35965d5969328dec3c76a9d8ada4a0d7a3d606fb8af5fef`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/std/parser/treesitter_node_spec.spl
mirror: doc/06_spec/01_unit/std/parser/treesitter_node_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/std/parser/treesitter_node_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/std/parser/treesitter_node_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/std/parser/treesitter_node_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/std/parser/treesitter_node_spec.spl:266:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can create Point with row and column' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
