# Ipynb Specification

> Tests covering ipynb_parse / ipynb_serialize.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ipynb Specification

## Scenarios

### ipynb_parse / ipynb_serialize

#### round-trips a serialized notebook back to an equal notebook

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- round-trips a serialized notebook back to an equal notebook
   - Expected: text2 equals `text1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round-trips a serialized notebook back to an equal notebook")
val nb = make_hello_notebook()
val text1 = ipynb_serialize(nb)
val parsed = ipynb_parse(text1)
match parsed:
    case Ok(nb2):
        val text2 = ipynb_serialize(nb2)
        expect(text2).to_equal(text1)
    case Err(msg):
        fail("expected parse to succeed, got error: {msg}")
```

</details>

#### serializes nbformat 4 with the expected structural markers

- serializes nbformat 4 with the expected structural markers


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("serializes nbformat 4 with the expected structural markers")
val nb = make_hello_notebook()
val text = ipynb_serialize(nb)
expect(text).to_contain("\"nbformat\": 4")
expect(text).to_contain("\"cell_type\": \"code\"")
expect(text).to_contain("\"cell_type\": \"markdown\"")
expect(text).to_contain("\"output_type\": \"stream\"")
```

</details>

#### preserves markdown source through the round trip

- preserves markdown source through the round trip
   - Expected: nb2.cells[0].cell_type equals `markdown`
   - Expected: nb2.cells[0].source equals `# Hello, Simple Lab`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("preserves markdown source through the round trip")
val nb = make_hello_notebook()
val text1 = ipynb_serialize(nb)
val parsed = ipynb_parse(text1)
match parsed:
    case Ok(nb2):
        expect(nb2.cells[0].cell_type).to_equal("markdown")
        expect(nb2.cells[0].source).to_equal("# Hello, Simple Lab")
    case Err(msg):
        fail("expected parse to succeed, got error: {msg}")
```

</details>

#### preserves code cell outputs through the round trip

- preserves code cell outputs through the round trip
   - Expected: code_cell.cell_type equals `code`
   - Expected: code_cell.execution_count equals `1`
   - Expected: code_cell.outputs.len() equals `1`
   - Expected: code_cell.outputs[0].output_type equals `stream`
   - Expected: code_cell.outputs[0].text equals `Hello, Simple Lab!\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("preserves code cell outputs through the round trip")
val nb = make_hello_notebook()
val text1 = ipynb_serialize(nb)
val parsed = ipynb_parse(text1)
match parsed:
    case Ok(nb2):
        val code_cell = nb2.cells[1]
        expect(code_cell.cell_type).to_equal("code")
        expect(code_cell.execution_count).to_equal(1)
        expect(code_cell.outputs.len()).to_equal(1)
        expect(code_cell.outputs[0].output_type).to_equal("stream")
        expect(code_cell.outputs[0].text).to_equal("Hello, Simple Lab!\n")
    case Err(msg):
        fail("expected parse to succeed, got error: {msg}")
```

</details>

#### fails fast on an unsupported nbformat version

- fails fast on an unsupported nbformat version


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails fast on an unsupported nbformat version")
val bad = "{\"nbformat\": 3, \"nbformat_minor\": 0, \"metadata\": {}, \"cells\": []}"
val parsed = ipynb_parse(bad)
match parsed:
    case Ok(_):
        fail("expected an Err for nbformat 3")
    case Err(msg):
        expect(msg).to_contain("nbformat")
```

</details>

#### fails fast on an unsupported cell_type

- fails fast on an unsupported cell_type


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails fast on an unsupported cell_type")
val bad = "{\"nbformat\": 4, \"nbformat_minor\": 5, \"metadata\": {}, \"cells\": [{\"cell_type\": \"raw\", \"metadata\": {}, \"source\": []}]}"
val parsed = ipynb_parse(bad)
match parsed:
    case Ok(_):
        fail("expected an Err for cell_type 'raw'")
    case Err(msg):
        expect(msg).to_contain("cell_type")
```

</details>

#### fails fast on an unsupported output_type

- fails fast on an unsupported output_type


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails fast on an unsupported output_type")
val bad = "{\"nbformat\": 4, \"nbformat_minor\": 5, \"metadata\": {}, \"cells\": [{\"cell_type\": \"code\", \"metadata\": {}, \"source\": [], \"execution_count\": null, \"outputs\": [{\"output_type\": \"execute_result\", \"data\": {}}]}]}"
val parsed = ipynb_parse(bad)
match parsed:
    case Ok(_):
        fail("expected an Err for output_type 'execute_result'")
    case Err(msg):
        expect(msg).to_contain("output_type")
```

</details>

#### fails fast on an unsupported display_data mimetype

- fails fast on an unsupported display_data mimetype


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails fast on an unsupported display_data mimetype")
val bad = "{\"nbformat\": 4, \"nbformat_minor\": 5, \"metadata\": {}, \"cells\": [{\"cell_type\": \"code\", \"metadata\": {}, \"source\": [], \"execution_count\": null, \"outputs\": [{\"output_type\": \"display_data\", \"data\": {\"image/png\": \"abc\"}, \"metadata\": {}}]}]}"
val parsed = ipynb_parse(bad)
match parsed:
    case Ok(_):
        fail("expected an Err for a non-text/plain display_data mimetype")
    case Err(msg):
        expect(msg).to_contain("mimetype")
```

</details>

#### fails fast on malformed JSON

- fails fast on malformed JSON


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails fast on malformed JSON")
val parsed = ipynb_parse("{not json")
match parsed:
    case Ok(_):
        fail("expected an Err for malformed JSON")
    case Err(msg):
        expect(msg).to_contain("JSON")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/notebook/ipynb_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ipynb_parse / ipynb_serialize.
- ipynb_parse / ipynb_serialize

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4fc4c218893306c5c33cdf74951db558e26691c1f26558a4bca4b3bc0e9509f3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4fc4c218893306c5c33cdf74951db558e26691c1f26558a4bca4b3bc0e9509f3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4fc4c218893306c5c33cdf74951db558e26691c1f26558a4bca4b3bc0e9509f3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/nogc_sync_mut/notebook/ipynb_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/notebook/ipynb_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/notebook/ipynb_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/notebook/ipynb_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/notebook/ipynb_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/notebook/ipynb_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips a serialized notebook back to an equal notebook' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/notebook/ipynb_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'serializes nbformat 4 with the expected structural markers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/notebook/ipynb_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves markdown source through the round trip' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
