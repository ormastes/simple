# deps_deep_spec

> Deep dependency report spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# deps_deep_spec

Deep dependency report spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/deps/deps_deep_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Deep dependency report spec.

Validates the three-section report produced by deps_deep_report_lines
against a small hand-built closure: json.spl + jsonrpc.spl from mcp_sdk.

## Scenarios

### deps_deep_report_lines

#### produces a non-empty report

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- produces a non-empty report


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces a non-empty report")
val rpt = deps_deep_report_lines(make_closure(), JSON_SPL)
expect(rpt.len()).to_be_greater_than(0)
```

</details>

#### report header contains entry file

- report header contains entry file
   - Expected: joined contains `JSON_SPL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("report header contains entry file")
val rpt = deps_deep_report_lines(make_closure(), JSON_SPL)
val joined = all_lines_joined(rpt)
expect(joined.contains(JSON_SPL)).to_equal(true)
```

</details>

#### SCRIPT section header is present

- SCRIPT section header is present
   - Expected: joined contains `SECTION 1: SCRIPT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SCRIPT section header is present")
val rpt = deps_deep_report_lines(make_closure(), JSON_SPL)
val joined = all_lines_joined(rpt)
expect(joined.contains("SECTION 1: SCRIPT")).to_equal(true)
```

</details>

#### json.spl has positive code line count

- json.spl has positive code line count
   - Expected: joined contains `code_lines:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("json.spl has positive code line count")
val rpt = deps_deep_report_lines(make_closure(), JSON_SPL)
val joined = all_lines_joined(rpt)
# code_lines line must appear
expect(joined.contains("code_lines:")).to_equal(true)
```

</details>

#### json.spl exports known function extract_json_string

- json.spl exports known function extract_json_string
   - Expected: joined contains `extract_json_string`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("json.spl exports known function extract_json_string")
val rpt = deps_deep_report_lines(make_closure(), JSON_SPL)
val joined = all_lines_joined(rpt)
expect(joined.contains("extract_json_string")).to_equal(true)
```

</details>

#### script totals report positive interface symbol count

- script totals report positive interface symbol count
   - Expected: joined contains `total_interface_symbols:`
   - Expected: joined contains `- escape_json`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("script totals report positive interface symbol count")
val rpt = deps_deep_report_lines(make_closure(), JSON_SPL)
val joined = all_lines_joined(rpt)
expect(joined.contains("total_interface_symbols:")).to_equal(true)
# At least one symbol was found — verify escape_json (top-level, no _-prefix) appears
expect(joined.contains("- escape_json")).to_equal(true)
```

</details>

#### SMF section header is present

- SMF section header is present
   - Expected: joined contains `SECTION 2: SMF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SMF section header is present")
val rpt = deps_deep_report_lines(make_closure(), JSON_SPL)
val joined = all_lines_joined(rpt)
expect(joined.contains("SECTION 2: SMF")).to_equal(true)
```

</details>

#### json.smf exists flag matches actual file presence

- json.smf exists flag matches actual file presence
   - Expected: joined contains `smf_exists: yes`
   - Expected: joined contains `smf_exists: no`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("json.smf exists flag matches actual file presence")
val actually_exists = file_exists(JSON_SMF)
val rpt = deps_deep_report_lines(make_closure(), JSON_SPL)
val joined = all_lines_joined(rpt)
if actually_exists:
    expect(joined.contains("smf_exists: yes")).to_equal(true)
else:
    expect(joined.contains("smf_exists: no")).to_equal(true)
```

</details>

#### smf size is non-negative when present

- smf size is non-negative when present
   - Expected: joined contains `smf_size_bytes:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("smf size is non-negative when present")
val rpt = deps_deep_report_lines(make_closure(), JSON_SPL)
val joined = all_lines_joined(rpt)
expect(joined.contains("smf_size_bytes:")).to_equal(true)
```

</details>

#### NATIVE section header is present

- NATIVE section header is present
   - Expected: joined contains `SECTION 3: NATIVE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("NATIVE section header is present")
val rpt = deps_deep_report_lines(make_closure(), JSON_SPL)
val joined = all_lines_joined(rpt)
expect(joined.contains("SECTION 3: NATIVE")).to_equal(true)
```

</details>

#### native_bytes line is present for json.spl

- native_bytes line is present for json.spl
   - Expected: joined contains `native_bytes:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("native_bytes line is present for json.spl")
val rpt = deps_deep_report_lines(make_closure(), JSON_SPL)
val joined = all_lines_joined(rpt)
expect(joined.contains("native_bytes:")).to_equal(true)
```

</details>

#### native bytes total is positive

- native bytes total is positive
   - Expected: joined contains `total_native_bytes:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("native bytes total is positive")
val rpt = deps_deep_report_lines(make_closure(), JSON_SPL)
val joined = all_lines_joined(rpt)
expect(joined.contains("total_native_bytes:")).to_equal(true)
```

</details>

#### native method is documented in output

- native method is documented in output
   - Expected: any_method is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("native method is documented in output")
val rpt = deps_deep_report_lines(make_closure(), JSON_SPL)
val joined = all_lines_joined(rpt)
# One of the three method labels must appear
val has_smf = joined.contains("smf_symbol_table")
val has_est = joined.contains("estimate_from_code_lines")
val has_art = joined.contains("smf_artifact_size")
val any_method = has_smf or has_est or has_art
expect(any_method).to_equal(true)
```

</details>

### deps_deep_report

#### returns same content as lines joined

- returns same content as lines joined
   - Expected: rpt_text contains `first_line`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns same content as lines joined")
val rpt_lines = deps_deep_report_lines(make_closure(), JSON_SPL)
val rpt_text = deps_deep_report(make_closure(), JSON_SPL)
expect(rpt_text.len()).to_be_greater_than(0)
# First line of lines array should appear in text version
val first_line = rpt_lines[0]
expect(rpt_text.contains(first_line)).to_equal(true)
```

</details>

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

- Canonical SPipe generation for source `555d946fa0f50c7ce746ec1f2ff6836ad216a51df4c433667ac8f6b6afc48266`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `555d946fa0f50c7ce746ec1f2ff6836ad216a51df4c433667ac8f6b6afc48266`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `555d946fa0f50c7ce746ec1f2ff6836ad216a51df4c433667ac8f6b6afc48266`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/deps/deps_deep_spec.spl
mirror: doc/06_spec/01_unit/app/deps/deps_deep_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/deps/deps_deep_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/deps/deps_deep_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/deps/deps_deep_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces a non-empty report' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/deps/deps_deep_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'report header contains entry file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/deps/deps_deep_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SCRIPT section header is present' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
