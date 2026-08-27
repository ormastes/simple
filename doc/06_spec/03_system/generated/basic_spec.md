# basic_spec

> Tests for the snapshot testing framework's basic functionality including

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# basic_spec

Tests for the snapshot testing framework's basic functionality including

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/generated/basic_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for the snapshot testing framework's basic functionality including
metadata storage, content comparison, supported formats, path generation,
and update mode handling.

## Scenarios

### Snapshot Testing Framework

#### Snapshot Metadata

#### stores snapshot name

- stores snapshot name
   - Expected: test_name equals `test_render`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stores snapshot name")
val test_name = "test_render"
expect(test_name).to_equal("test_render")
```

</details>

#### stores snapshot format

- stores snapshot format
   - Expected: format equals `text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stores snapshot format")
val format = "text"
expect(format).to_equal("text")
```

</details>

#### stores snapshot content

- stores snapshot content
   - Expected: content equals `Hello World`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stores snapshot content")
val content = "Hello World"
expect(content).to_equal("Hello World")
```

</details>

#### Snapshot Comparison

#### identifies matching content

- identifies matching content
   - Expected: content1 equals `content2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("identifies matching content")
val content1 = "same content"
val content2 = "same content"
expect(content1).to_equal(content2)
```

</details>

#### identifies different content

- identifies different content


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("identifies different content")
val content1 = "content A"
val content2 = "content B"
expect(content1).to_not_equal(content2)
```

</details>

#### Snapshot Formats

#### supports text format

- supports text format
   - Expected: format equals `text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports text format")
val format = "text"
expect(format).to_equal("text")
```

</details>

#### supports json format

- supports json format
   - Expected: format equals `json`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports json format")
val format = "json"
expect(format).to_equal("json")
```

</details>

#### supports yaml format

- supports yaml format
   - Expected: format equals `yaml`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports yaml format")
val format = "yaml"
expect(format).to_equal("yaml")
```

</details>

#### Snapshot Paths

#### generates snapshot path

- generates snapshot path
   - Expected: test_file contains `expected_contains`
   - Expected: test_name equals `test_render`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates snapshot path")
val test_file = "test/example_spec.spl"
val test_name = "test_render"
val expected_contains = "example_spec"
expect(test_file.contains(expected_contains)).to_equal(true)
expect(test_name).to_equal("test_render")
```

</details>

#### Snapshot Updates

#### marks snapshot for update

- marks snapshot for update
   - Expected: should_update is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("marks snapshot for update")
val should_update = true
expect(should_update).to_equal(true)
```

</details>

#### skips update when disabled

- skips update when disabled
   - Expected: should_update is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("skips update when disabled")
val should_update = false
expect(should_update).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7af8e5233b3a56ab1d7ec0bbeaef857b20ef1445f0cfe52f64c8fb0fd9633372`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7af8e5233b3a56ab1d7ec0bbeaef857b20ef1445f0cfe52f64c8fb0fd9633372`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7af8e5233b3a56ab1d7ec0bbeaef857b20ef1445f0cfe52f64c8fb0fd9633372`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/generated/basic_spec.spl
mirror: doc/06_spec/03_system/generated/basic_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/generated/basic_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/generated/basic_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/generated/basic_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stores snapshot name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/generated/basic_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stores snapshot format' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/generated/basic_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stores snapshot content' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
