# Text negative single-index Specification

> Pins CHARACTER-indexed text single-indexing with Python-style negative indices, in both engines. Single-index (`s[i]`, `char_at`) keeps character semantics — the deliberate outlier family — while slices, len and index_of are byte-indexed.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Text negative single-index Specification

Pins CHARACTER-indexed text single-indexing with Python-style negative indices, in both engines. Single-index (`s[i]`, `char_at`) keeps character semantics — the deliberate outlier family — while slices, len and index_of are byte-indexed.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #INTERP-TEXT-NEG-INDEX-001 |
| Category | Runtime |
| Difficulty | 2/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | doc/08_tracking/bug/test_harness_execution_divergence_2026-07-29.md |
| Source | `test/01_unit/bugs/text_negative_single_index_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Pins CHARACTER-indexed text single-indexing with Python-style negative
indices, in both engines. Single-index (`s[i]`, `char_at`) keeps
character semantics — the deliberate outlier family — while slices, len
and index_of are byte-indexed.

Before the fix the JIT lane's rt_string_char_at returned NIL for any
negative index ("aé🙂z"[-2] was nil under the default engine while the
interpreter returned "🙂"). This spec runs under bin/simple test's
forced-interpret lane; the JIT half of the A/B is pinned by probes in
the bug doc.

## Scenarios

### text single-index character semantics

#### positive indices are character-indexed

#### returns the multi-byte character at index 1

- returns the multi-byte character at index 1
   - Expected: v[1] equals `é`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns the multi-byte character at index 1")
val v = "aé🙂z"
expect(v[1]).to_equal("é")
```

</details>

#### returns the 4-byte emoji at index 2

- returns the 4-byte emoji at index 2
   - Expected: v[2] equals `🙂`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns the 4-byte emoji at index 2")
val v = "aé🙂z"
expect(v[2]).to_equal("🙂")
```

</details>

#### negative indices count characters from the end

#### returns the last character for -1

- returns the last character for -1
   - Expected: v[-1] equals `z`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns the last character for -1")
val v = "aé🙂z"
expect(v[-1]).to_equal("z")
```

</details>

#### returns the 4-byte emoji for -2

- returns the 4-byte emoji for -2
   - Expected: v[-2] equals `🙂`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns the 4-byte emoji for -2")
val v = "aé🙂z"
expect(v[-2]).to_equal("🙂")
```

</details>

#### returns the first character for -len

- returns the first character for -len
   - Expected: v[-4] equals `a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns the first character for -len")
val v = "aé🙂z"
expect(v[-4]).to_equal("a")
```

</details>

#### agreement between forms

#### v[-2] equals v[len_chars - 2]

- v[-2] equals v[len_chars - 2]
   - Expected: v[-2] equals `v[2]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("v[-2] equals v[len_chars - 2]")
val v = "aé🙂z"
expect(v[-2]).to_equal(v[2])
```

</details>

#### vacuity probe

#### executes assertions in this file

- executes assertions in this file
   - Expected: v[-1] equals `y`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes assertions in this file")
val v = "vacuity"
expect(v[-1]).to_equal("y")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Research:** `doc/08_tracking/bug/test_harness_execution_divergence_2026-07-29.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `069ae852ca2bcb991faff2f72e97d410230337d70863cdcafc1927c8f150218d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `069ae852ca2bcb991faff2f72e97d410230337d70863cdcafc1927c8f150218d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `069ae852ca2bcb991faff2f72e97d410230337d70863cdcafc1927c8f150218d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/bugs/text_negative_single_index_spec.spl
mirror: doc/06_spec/01_unit/bugs/text_negative_single_index_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/bugs/text_negative_single_index_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/bugs/text_negative_single_index_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/bugs/text_negative_single_index_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the multi-byte character at index 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/bugs/text_negative_single_index_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the 4-byte emoji at index 2' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/bugs/text_negative_single_index_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the last character for -1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
