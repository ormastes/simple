# Text Presence Functions Specification

> Tests `presence` and `presence_trimmed` functions that convert text to `text?`, returning the value if non-empty/non-blank, or `nil` otherwise.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Text Presence Functions Specification

Tests `presence` and `presence_trimmed` functions that convert text to `text?`, returning the value if non-empty/non-blank, or `nil` otherwise.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #2100-PRESENCE |
| Category | Stdlib |
| Difficulty | 1/5 |
| Status | Implemented |
| Research | doc/01_research/text_validity_presence_pattern_2026-02-24.md |
| Source | `test/01_unit/lib/common/text_empty_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests `presence` and `presence_trimmed` functions that convert text to `text?`,
returning the value if non-empty/non-blank, or `nil` otherwise.

## Note

Functions are defined locally because importing `lib.common.text` causes
timeout (~40s) due to heavy transitive dependencies. The canonical source
is `src/lib/common/text.spl`. These local copies mirror that implementation.

## Scenarios

### presence

#### returns value for non-empty

- returns value for non-empty
   - Expected: presence("hello") ?? "" equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns value for non-empty")
"""Returns the original string when it has content."""
expect(presence("hello") ?? "").to_equal("hello")
```

</details>

#### returns nil for empty

- returns nil for empty
   - Expected: presence("") ?? "default" equals `default`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns nil for empty")
"""Returns nil for empty string, enabling ?? fallback."""
expect(presence("") ?? "default").to_equal("default")
```

</details>

#### returns whitespace string

- returns whitespace string
   - Expected: presence("  ") ?? "" equals `  `


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns whitespace string")
"""Whitespace-only strings are non-empty (use presence_trimmed for blank check)."""
expect(presence("  ") ?? "").to_equal("  ")
```

</details>

### presence_trimmed

#### returns value for non-blank

- returns value for non-blank
   - Expected: presence_trimmed("hello") ?? "" equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns value for non-blank")
"""Returns string when it has meaningful (non-whitespace) content."""
expect(presence_trimmed("hello") ?? "").to_equal("hello")
```

</details>

#### returns nil for empty

- returns nil for empty
   - Expected: presence_trimmed("") ?? "default" equals `default`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns nil for empty")
"""Returns nil for empty string."""
expect(presence_trimmed("") ?? "default").to_equal("default")
```

</details>

#### returns nil for whitespace-only

- returns nil for whitespace-only
   - Expected: presence_trimmed("  ") ?? "default" equals `default`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns nil for whitespace-only")
"""Returns nil for strings with only whitespace characters."""
expect(presence_trimmed("  ") ?? "default").to_equal("default")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Research:** `doc/01_research/text_validity_presence_pattern_2026-02-24.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2624e23a29d2b8e0c5772c6fbd2476b8b30df3dd38abe5587c8fb49133ea63db`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2624e23a29d2b8e0c5772c6fbd2476b8b30df3dd38abe5587c8fb49133ea63db`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2624e23a29d2b8e0c5772c6fbd2476b8b30df3dd38abe5587c8fb49133ea63db`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/text_empty_spec.spl
mirror: doc/06_spec/01_unit/lib/common/text_empty_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/text_empty_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/text_empty_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/text_empty_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns value for non-empty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/text_empty_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns nil for empty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/text_empty_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns whitespace string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
