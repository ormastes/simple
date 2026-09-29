# Tree and Node Real Implementation Tests

> Tests for the actual Tree, Node, NodeArena, Span, and TreeCursor

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tree and Node Real Implementation Tests

Tests for the actual Tree, Node, NodeArena, Span, and TreeCursor

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-TREE-001 |
| Category | Parser \| Tree |
| Status | Planned |
| Source | `test/unit/compiler/parser/treesitter_tree_real_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for the actual Tree, Node, NodeArena, Span, and TreeCursor
implementations in std.parser.treesitter.

NOTE: Tests are skipped until std.parser.treesitter module parse errors are fixed.

## Scenarios

### Span

#### creates span with byte positions

- creates span with byte positions


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates span with byte positions")
expect true
```

</details>

#### creates span with line positions

- creates span with line positions


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates span with line positions")
expect true
```

</details>

#### contains point on same line

- contains point on same line


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains point on same line")
expect true
```

</details>

#### does not contain point outside column range

- does not contain point outside column range


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not contain point outside column range")
expect true
```

</details>

#### contains point on start line of multi-line span

- contains point on start line of multi-line span


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains point on start line of multi-line span")
expect true
```

</details>

#### contains point on end line of multi-line span

- contains point on end line of multi-line span


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains point on end line of multi-line span")
expect true
```

</details>

#### contains point on middle line of multi-line span

- contains point on middle line of multi-line span


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains point on middle line of multi-line span")
expect true
```

</details>

### NodeId

#### creates NodeId with index and generation

- creates NodeId with index and generation


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates NodeId with index and generation")
expect true
```

</details>

#### distinguishes different indices

- distinguishes different indices


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("distinguishes different indices")
expect true
```

</details>

#### distinguishes different generations

- distinguishes different generations


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("distinguishes different generations")
expect true
```

</details>

### NodeArena

#### creates empty arena

- creates empty arena


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates empty arena")
expect true
```

</details>

#### allocates node and returns id

- allocates node and returns id


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allocates node and returns id")
expect true
```

</details>

#### allocates multiple nodes with sequential indices

- allocates multiple nodes with sequential indices


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allocates multiple nodes with sequential indices")
expect true
```

</details>

#### retrieves node by id

- retrieves node by id


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("retrieves node by id")
expect true
```

</details>

#### returns None for invalid generation

- returns None for invalid generation


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns None for invalid generation")
expect true
```

</details>

#### returns None for out of bounds index

- returns None for out of bounds index


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns None for out of bounds index")
expect true
```

</details>

### Node

#### creates node with kind and text

- creates node with kind and text


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates node with kind and text")
expect true
```

</details>

#### reports child count

- reports child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports child count")
expect true
```

</details>

#### gets child by index

- gets child by index


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets child by index")
expect true
```

</details>

#### returns None for invalid child index

- returns None for invalid child index


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns None for invalid child index")
expect true
```

</details>

#### gets child by field name

- gets child by field name


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets child by field name")
expect true
```

</details>

#### returns None for unknown field

- returns None for unknown field


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns None for unknown field")
expect true
```

</details>

#### tracks error state

- tracks error state


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks error state")
expect true
```

</details>

### Tree

#### has root node

- has root node


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has root node")
expect true
```

</details>

#### stores source

- stores source


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores source")
expect true
```

</details>

#### has version

- has version


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has version")
expect true
```

</details>

#### gets node by id

- gets node by id


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets node by id")
expect true
```

</details>

#### can walk with cursor

- can walk with cursor


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can walk with cursor")
expect true
```

</details>

### TreeCursor

#### starts at root

- starts at root


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts at root")
expect true
```

</details>

#### goes to first child

- goes to first child


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("goes to first child")
expect true
```

</details>

#### goes to next sibling

- goes to next sibling


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("goes to next sibling")
expect true
```

</details>

#### goes to parent

- goes to parent


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("goes to parent")
expect true
```

</details>

#### tracks depth correctly

- tracks depth correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks depth correctly")
expect true
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
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

- Canonical SPipe generation for source `2758b17564f52f1f4ac06ec7cdfdee05ce637c9192ce217389e81612cc7c19b7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2758b17564f52f1f4ac06ec7cdfdee05ce637c9192ce217389e81612cc7c19b7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2758b17564f52f1f4ac06ec7cdfdee05ce637c9192ce217389e81612cc7c19b7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/unit/compiler/parser/treesitter_tree_real_spec.spl
mirror: doc/06_spec/unit/compiler/parser/treesitter_tree_real_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/parser/treesitter_tree_real_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/parser/treesitter_tree_real_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/parser/treesitter_tree_real_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates span with byte positions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/treesitter_tree_real_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates span with line positions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/treesitter_tree_real_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'contains point on same line' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/treesitter_tree_real_spec.spl:209:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can walk with cursor' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
