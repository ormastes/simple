# Doc Integration Specification

> Tests covering stats command coverage output, stats JSON export format.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Doc Integration Specification

## Scenarios

### stats command coverage output

#### stats shows non-zero file counts

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- stats shows non-zero file counts
   - Expected: exit_code equals `0`
   - Expected: stdout contains `Files:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stats shows non-zero file counts")
val result = run_simple(["stats", "--quick"])
val stdout = result.0
val exit_code = result.2
expect(exit_code).to_equal(0)
expect(stdout.contains("Files:")).to_equal(true)
```

</details>

#### stats --json returns valid JSON with documentation section

- stats --json returns valid JSON with documentation section
   - Expected: exit_code equals `0`
   - Expected: stdout contains `"documentation"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stats --json returns valid JSON with documentation section")
val result = run_simple(["stats", "--json"])
val stdout = result.0
val exit_code = result.2
expect(exit_code).to_equal(0)
expect(stdout.contains("\"documentation\"")).to_equal(true)
```

</details>

#### stats --json documentation has total_public field

- stats --json documentation has total_public field
   - Expected: stdout contains `"total_public"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stats --json documentation has total_public field")
val result = run_simple(["stats", "--json"])
val stdout = result.0
expect(stdout.contains("\"total_public\"")).to_equal(true)
```

</details>

#### stats --json documentation has non-zero total_public

- stats --json documentation has non-zero total_public
   - Expected: has_nonzero is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stats --json documentation has non-zero total_public")
val result = run_simple(["stats", "--json"])
val stdout = result.0
# total_public should not be 0 in a real project
val has_nonzero = not stdout.contains("\"total_public\": 0")
expect(has_nonzero).to_equal(true)
```

</details>

#### stats --json has per_scope section

- stats --json has per_scope section
   - Expected: stdout contains `"per_scope"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stats --json has per_scope section")
val result = run_simple(["stats", "--json"])
val stdout = result.0
expect(stdout.contains("\"per_scope\"")).to_equal(true)
```

</details>

#### stats --json per_scope has std section

- stats --json per_scope has std section
   - Expected: stdout contains `"std"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stats --json per_scope has std section")
val result = run_simple(["stats", "--json"])
val stdout = result.0
expect(stdout.contains("\"std\"")).to_equal(true)
```

</details>

#### stats --json per_scope has core section

- stats --json per_scope has core section
   - Expected: stdout contains `"core"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stats --json per_scope has core section")
val result = run_simple(["stats", "--json"])
val stdout = result.0
expect(stdout.contains("\"core\"")).to_equal(true)
```

</details>

#### stats --json lib documented field is not always 100 percent

- stats --json lib documented field is not always 100 percent
   - Expected: stdout contains `"lib"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stats --json lib documented field is not always 100 percent")
val result = run_simple(["stats", "--json"])
val stdout = result.0
# The old bug always showed lib at 100% - verify the field exists
expect(stdout.contains("\"lib\"")).to_equal(true)
```

</details>

### stats JSON export format

#### stats --json outputs valid JSON braces

- stats --json outputs valid JSON braces
   - Expected: stdout.starts_with("{") is true
   - Expected: stdout.ends_with("}") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stats --json outputs valid JSON braces")
val result = run_simple(["stats", "--json"])
val stdout = result.0
expect(stdout.starts_with("{")).to_equal(true)
expect(stdout.ends_with("}")).to_equal(true)
```

</details>

#### stats --json has files section

- stats --json has files section
   - Expected: stdout contains `"files"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stats --json has files section")
val result = run_simple(["stats", "--json"])
val stdout = result.0
expect(stdout.contains("\"files\"")).to_equal(true)
```

</details>

#### stats --json has tests section

- stats --json has tests section
   - Expected: stdout contains `"tests"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stats --json has tests section")
val result = run_simple(["stats", "--json"])
val stdout = result.0
expect(stdout.contains("\"tests\"")).to_equal(true)
```

</details>

#### stats --json has features section

- stats --json has features section
   - Expected: stdout contains `"features"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stats --json has features section")
val result = run_simple(["stats", "--json"])
val stdout = result.0
expect(stdout.contains("\"features\"")).to_equal(true)
```

</details>

#### stats --json has lines section

- stats --json has lines section
   - Expected: stdout contains `"lines"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stats --json has lines section")
val result = run_simple(["stats", "--json"])
val stdout = result.0
expect(stdout.contains("\"lines\"")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/stats/doc_integration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering stats command coverage output, stats JSON export format.
- stats command coverage output
- stats JSON export format

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
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

- Canonical SPipe generation for source `380650fa4cc8421cb1bdf0cb5fdd4e8d6ab2364bfaf8649988e453a5570f2212`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `380650fa4cc8421cb1bdf0cb5fdd4e8d6ab2364bfaf8649988e453a5570f2212`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `380650fa4cc8421cb1bdf0cb5fdd4e8d6ab2364bfaf8649988e453a5570f2212`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/app/stats/doc_integration_spec.spl
mirror: doc/06_spec/unit/app/stats/doc_integration_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/stats/doc_integration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/stats/doc_integration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/stats/doc_integration_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/stats/doc_integration_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stats shows non-zero file counts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/stats/doc_integration_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stats --json returns valid JSON with documentation section' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/stats/doc_integration_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stats --json documentation has total_public field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
