# spec_gen_drop_and_path_spec

> spec-gen drop-and-path regression spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# spec_gen_drop_and_path_spec

spec-gen drop-and-path regression spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/spec_gen/spec_gen_drop_and_path_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

spec-gen drop-and-path regression spec.

Reproduces the two filed defects in bin/simple spec-gen
(doc/08_tracking/bug/spec_gen_flattens_output_and_silently_drops_specs_2026-08-18.md):

1. Paren-form it blocks -- and triple-quote doc-block openers that carry text on
   the same line -- extracted nothing, and the file was skipped in silence.
2. spec_relative_dir stripped the user-supplied search path, flattening output
   into the doc/06_spec root instead of the test/ mirror path.

## Scenarios

### spec-gen extraction covers the paren block form

#### extracts it(\

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- extracts it(\
   - Expected: doc contains `## paren suite`
   - Expected: doc contains `- does a paren thing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts it(\")
val src = "describe(\"paren suite\"):\n    it(\"does a paren thing\"):\n        pass\n"
val doc = extract_spec_doc(src, "x_spec.spl")
expect(doc.contains("## paren suite")).to_equal(true)
expect(doc.contains("- does a paren thing")).to_equal(true)
```

</details>

#### still extracts the bare block form

- still extracts the bare block form
   - Expected: doc contains `## bare suite`
   - Expected: doc contains `- does a bare thing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still extracts the bare block form")
val src = "describe \"bare suite\":\n    it \"does a bare thing\":\n        pass\n"
val doc = extract_spec_doc(src, "x_spec.spl")
expect(doc.contains("## bare suite")).to_equal(true)
expect(doc.contains("- does a bare thing")).to_equal(true)
```

</details>

#### does not swallow the file when the doc block opener carries text

- does not swallow the file when the doc block opener carries text
   - Expected: doc.trim() == "" is false
   - Expected: doc contains `## after doc block`
   - Expected: doc contains `- is still extracted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not swallow the file when the doc block opener carries text")
val src = "\"\"\"Title line.\n\nMore prose.\n\"\"\"\n\ndescribe \"after doc block\":\n    it \"is still extracted\":\n        pass\n"
val doc = extract_spec_doc(src, "x_spec.spl")
expect(doc.trim() == "").to_equal(false)
expect(doc.contains("## after doc block")).to_equal(true)
expect(doc.contains("- is still extracted")).to_equal(true)
```

</details>

### spec-gen mirrors test/ paths regardless of the scope argument

#### keeps the full mirror path for a scoped file

- keeps the full mirror path for a scoped file


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the full mirror path for a scoped file")
expect(spec_relative_dir("test/01_unit/app/office/sheets/validation_spec.spl"))
    .to_equal("01_unit/app/office/sheets")
```

</details>

#### resolves the mirror path from the repo test/ root

- resolves the mirror path from the repo test/ root


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves the mirror path from the repo test/ root")
expect(spec_relative_dir("test/01_unit/app/office/calc_cli_spec.spl"))
    .to_equal("01_unit/app/office")
```

</details>

#### handles an absolute path containing /test/

- handles an absolute path containing /test/


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles an absolute path containing /test/")
expect(spec_relative_dir("/repo/test/01_unit/app/office/calc_cli_spec.spl"))
    .to_equal("01_unit/app/office")
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `28265444f3df8c690f6adb8ed15f808987df000371aec6cee4a4e57f372c81e3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `28265444f3df8c690f6adb8ed15f808987df000371aec6cee4a4e57f372c81e3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `28265444f3df8c690f6adb8ed15f808987df000371aec6cee4a4e57f372c81e3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/spec_gen/spec_gen_drop_and_path_spec.spl
mirror: doc/06_spec/01_unit/app/spec_gen/spec_gen_drop_and_path_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/spec_gen/spec_gen_drop_and_path_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/spec_gen/spec_gen_drop_and_path_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/spec_gen/spec_gen_drop_and_path_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts it(\' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/spec_gen/spec_gen_drop_and_path_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still extracts the bare block form' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/spec_gen/spec_gen_drop_and_path_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not swallow the file when the doc block opener carries text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
