# SmfSource Specification

> Tests for the SmfSource enum — unified abstraction for file-backed and in-memory SMF modules.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SmfSource Specification

Tests for the SmfSource enum — unified abstraction for file-backed and in-memory SMF modules.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SMF-009 |
| Category | Infrastructure |
| Difficulty | 1/5 |
| Status | In Progress |
| Plan | doc/03_plan/smf_load_enable_plan.md |
| Source | `test/unit/compiler/interpreter/smf_source_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the SmfSource enum — unified abstraction for file-backed
and in-memory SMF modules.

## Scenarios

### SmfSource

#### creates file source and reports name

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates file source and reports name
   - Expected: smf_source_get_name(src) equals `/cache/mod.smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates file source and reports name")
val src = SmfSource.FileSmf(path: "/cache/mod.smf")
expect(smf_source_get_name(src)).to_equal("/cache/mod.smf")
```

</details>

#### creates memory source and reports name

- creates memory source and reports name
   - Expected: smf_source_get_name(src) equals `std.text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates memory source and reports name")
val bytes: [u8] = [0, 1, 2, 3]
val src = SmfSource.MemorySmf(bytes: bytes, logical_name: "std.text")
expect(smf_source_get_name(src)).to_equal("std.text")
```

</details>

#### identifies file source correctly

- identifies file source correctly
   - Expected: smf_source_is_file(src) is true
   - Expected: smf_source_is_memory(src) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies file source correctly")
val src = SmfSource.FileSmf(path: "/a.smf")
expect(smf_source_is_file(src)).to_equal(true)
expect(smf_source_is_memory(src)).to_equal(false)
```

</details>

#### identifies memory source correctly

- identifies memory source correctly
   - Expected: smf_source_is_file(src) is false
   - Expected: smf_source_is_memory(src) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies memory source correctly")
val bytes: [u8] = [0]
val src = SmfSource.MemorySmf(bytes: bytes, logical_name: "m")
expect(smf_source_is_file(src)).to_equal(false)
expect(smf_source_is_memory(src)).to_equal(true)
```

</details>

#### returns file path for file source

- returns file path for file source
   - Expected: smf_source_file_path(src) equals `/cache/x.smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns file path for file source")
val src = SmfSource.FileSmf(path: "/cache/x.smf")
expect(smf_source_file_path(src)).to_equal("/cache/x.smf")
```

</details>

#### returns empty path for memory source

- returns empty path for memory source
   - Expected: smf_source_file_path(src) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty path for memory source")
val bytes: [u8] = [0]
val src = SmfSource.MemorySmf(bytes: bytes, logical_name: "m")
expect(smf_source_file_path(src)).to_equal("")
```

</details>

#### describes file source

- describes file source


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes file source")
val src = SmfSource.FileSmf(path: "/a.smf")
expect(smf_source_describe(src)).to_start_with("file:")
```

</details>

#### describes memory source

- describes memory source


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes memory source")
val bytes: [u8] = [0]
val src = SmfSource.MemorySmf(bytes: bytes, logical_name: "mod")
expect(smf_source_describe(src)).to_start_with("memory:")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/smf_load_enable_plan.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e8fd0111b4bb734e8e653c8231cc62c7980af25a581c6c608a1f8f6e6de5ce6f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e8fd0111b4bb734e8e653c8231cc62c7980af25a581c6c608a1f8f6e6de5ce6f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e8fd0111b4bb734e8e653c8231cc62c7980af25a581c6c608a1f8f6e6de5ce6f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/interpreter/smf_source_spec.spl
mirror: doc/06_spec/unit/compiler/interpreter/smf_source_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/interpreter/smf_source_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/interpreter/smf_source_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/interpreter/smf_source_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates file source and reports name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/interpreter/smf_source_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates memory source and reports name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/interpreter/smf_source_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'identifies file source correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
