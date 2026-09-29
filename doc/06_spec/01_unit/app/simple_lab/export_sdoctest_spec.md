# Export Sdoctest Specification

> Tests covering nb_to_sdoctest_markdown, exported fences round-trip through the real sdoctest extractor, export_notebook_file (hello fixture, end to end).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Export Sdoctest Specification

## Scenarios

### nb_to_sdoctest_markdown

#### passes markdown cells through unchanged

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- passes markdown cells through unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("passes markdown cells through unchanged")
val nb = make_hello_notebook()
val md = nb_to_sdoctest_markdown(nb)
expect(md).to_contain("# Hello, Simple Lab")
```

</details>

#### wraps code cells in an sdoctest fence with prompted source lines

- wraps code cells in an sdoctest fence with prompted source lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("wraps code cells in an sdoctest fence with prompted source lines")
val nb = make_hello_notebook()
val md = nb_to_sdoctest_markdown(nb)
expect(md).to_contain("```sdoctest")
expect(md).to_contain(">>> print(\"Hello, Simple Lab!\")")
expect(md).to_contain("```")
```

</details>

#### includes the captured output beneath the prompt

- includes the captured output beneath the prompt


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("includes the captured output beneath the prompt")
val nb = make_hello_notebook()
val md = nb_to_sdoctest_markdown(nb)
expect(md).to_contain("Hello, Simple Lab!")
```

</details>

### exported fences round-trip through the real sdoctest extractor

#### recovers a single-line code cell's source exactly

- recovers a single-line code cell's source exactly
   - Expected: blocks.len() equals `1`
   - Expected: blocks[0].code equals `cell.source`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("recovers a single-line code cell's source exactly")
val cell = NbCell(
    cell_type: "code",
    metadata_json: "{}",
    source: "print(\"Hello, Simple Lab!\")",
    has_execution_count: true,
    execution_count: 1,
    outputs: []
)
val nb = NbNotebook(nbformat_minor: 5, metadata_json: "{}", cells: [cell])
val md = nb_to_sdoctest_markdown(nb)
val blocks = extract_blocks_from_content(md, "x.md")
expect(blocks.len()).to_equal(1)
expect(blocks[0].code).to_equal(cell.source)
```

</details>

#### recovers a multi-line code cell's source, including indentation and a blank line

- recovers a multi-line code cell's source, including indentation and a blank line
   - Expected: blocks.len() equals `1`
   - Expected: blocks[0].code equals `multiline_source`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("recovers a multi-line code cell's source, including indentation and a blank line")
val multiline_source = "if 1 > 0:\n    print(\"yes\")\n\nprint(\"done\")"
val cell = NbCell(
    cell_type: "code",
    metadata_json: "{}",
    source: multiline_source,
    has_execution_count: true,
    execution_count: 1,
    outputs: []
)
val nb = NbNotebook(nbformat_minor: 5, metadata_json: "{}", cells: [cell])
val md = nb_to_sdoctest_markdown(nb)
val blocks = extract_blocks_from_content(md, "x.md")
expect(blocks.len()).to_equal(1)
expect(blocks[0].code).to_equal(multiline_source)
```

</details>

#### marks an errored cell should_fail so the exported doc still has a real verdict

- marks an errored cell should_fail so the exported doc still has a real verdict


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("marks an errored cell should_fail so the exported doc still has a real verdict")
val error_output = NbOutput(
    output_type: "error",
    stream_name: "",
    text: "",
    metadata_json: "{}",
    ename: "ValueError",
    evalue: "boom",
    traceback: ""
)
val cell = NbCell(
    cell_type: "code",
    metadata_json: "{}",
    source: "raise_boom()",
    has_execution_count: true,
    execution_count: 1,
    outputs: [error_output]
)
val nb = NbNotebook(nbformat_minor: 5, metadata_json: "{}", cells: [cell])
val md = nb_to_sdoctest_markdown(nb)
expect(md).to_contain("```sdoctest:should_fail")
```

</details>

### export_notebook_file (hello fixture, end to end)

#### writes the hello-world fixture notebook

- writes the hello-world fixture notebook
   - Expected: wrote is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("writes the hello-world fixture notebook")
val nb = make_hello_notebook()
val ipynb_text = ipynb_serialize(nb)
val wrote = file_write(FIXTURE_IPYNB, ipynb_text)
expect(wrote).to_equal(true)
```

</details>

#### exports the fixture to an sdoctest markdown file

- exports the fixture to an sdoctest markdown file
   - Expected: comparison.status equals `EvidenceStatus.passed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("exports the fixture to an sdoctest markdown file")
val result = export_notebook_file(FIXTURE_IPYNB, FIXTURE_SDOCTEST_MD)
match result:
    case Ok(_):
        pass_do_nothing
    case Err(msg):
        fail("expected export to succeed, got error: {msg}")
val written = file_read(FIXTURE_SDOCTEST_MD)
expect(written).to_contain("```sdoctest")

val capture = UntypedCapture(label: "hello-sdoctest-md", raw_value: written, source_kind: "log_line")
val evidence = untyped_capture_to_canonical(capture, "export_sdoctest_spec/hello-sdoctest-md")
val comparison = compare_evidence(evidence, oracle_spec("export_sdoctest_spec/hello-sdoctest-md", [
    check_exact("value", "# Hello, Simple Lab\n\nA minimal notebook used to verify the sdoctest exporter.\n\n```sdoctest\n>>> print(\"Hello, Simple Lab!\")\nHello, Simple Lab!\n\n```")
]))
expect(comparison.status).to_equal(EvidenceStatus.passed)
```

</details>

#### produces output that passes `simple test --sdoctest`

- produces output that passes `simple test --sdoctest`
   - Expected: exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("produces output that passes `simple test --sdoctest`")
val run_result = process_run_bounded("bin/simple", ["test", "--sdoctest", FIXTURE_SDOCTEST_MD], 30000, 65536)
val stdout = run_result.0
val stderr = run_result.1
val exit_code = run_result.2
if exit_code != 0:
    fail("bin/simple test --sdoctest {FIXTURE_SDOCTEST_MD} exited {exit_code}\nstdout: {stdout}\nstderr: {stderr}")
expect(exit_code).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/simple_lab/export_sdoctest_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nb_to_sdoctest_markdown, exported fences round-trip through the real sdoctest extractor, export_notebook_file (hello fixture, end to end).
- nb_to_sdoctest_markdown
- exported fences round-trip through the real sdoctest extractor
- export_notebook_file (hello fixture, end to end)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ab702f427aa1a7e42e16c22b540cfbb4e9524f3b398eb866ec66c8b40f3b7d01`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ab702f427aa1a7e42e16c22b540cfbb4e9524f3b398eb866ec66c8b40f3b7d01`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ab702f427aa1a7e42e16c22b540cfbb4e9524f3b398eb866ec66c8b40f3b7d01`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/simple_lab/export_sdoctest_spec.spl
mirror: doc/06_spec/01_unit/app/simple_lab/export_sdoctest_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/app/simple_lab/export_sdoctest_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/simple_lab/export_sdoctest_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/simple_lab/export_sdoctest_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/simple_lab/export_sdoctest_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/simple_lab/export_sdoctest_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes markdown cells through unchanged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/simple_lab/export_sdoctest_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'wraps code cells in an sdoctest fence with prompted source lines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/simple_lab/export_sdoctest_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes the captured output beneath the prompt' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
