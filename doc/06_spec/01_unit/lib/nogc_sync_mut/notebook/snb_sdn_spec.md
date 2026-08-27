# Snb Sdn Specification

> Tests covering snb_serialize / snb_parse, ipynb <-> snb.sdn lossless conversion.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Snb Sdn Specification

## Scenarios

### snb_serialize / snb_parse

#### round-trips a notebook through SDN text unchanged

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- round-trips a notebook through SDN text unchanged
   - Expected: snb_text2 equals `snb_text1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round-trips a notebook through SDN text unchanged")
val nb = make_hello_notebook()
val snb_text1 = snb_serialize(nb)
val parsed = snb_parse(snb_text1)
match parsed:
    case Ok(nb2):
        val snb_text2 = snb_serialize(nb2)
        expect(snb_text2).to_equal(snb_text1)
    case Err(msg):
        fail("expected snb_parse to succeed, got error: {msg}")
```

</details>

#### preserves cell content through the SDN round trip

- preserves cell content through the SDN round trip
   - Expected: nb2.cells.len() equals `2`
   - Expected: nb2.cells[0].source equals `# Hello, Simple Lab`
   - Expected: nb2.cells[1].source equals `print("Hello, Simple Lab!")`
   - Expected: nb2.cells[1].outputs[0].text equals `Hello, Simple Lab!\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("preserves cell content through the SDN round trip")
val nb = make_hello_notebook()
val parsed = snb_parse(snb_serialize(nb))
match parsed:
    case Ok(nb2):
        expect(nb2.cells.len()).to_equal(2)
        expect(nb2.cells[0].source).to_equal("# Hello, Simple Lab")
        expect(nb2.cells[1].source).to_equal("print(\"Hello, Simple Lab!\")")
        expect(nb2.cells[1].outputs[0].text).to_equal("Hello, Simple Lab!\n")
    case Err(msg):
        fail("expected snb_parse to succeed, got error: {msg}")
```

</details>

#### fails fast on an unsupported cell_type in SDN

- fails fast on an unsupported cell_type in SDN


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails fast on an unsupported cell_type in SDN")
val parsed = snb_parse("{snb_version: 1, nbformat_minor: 5, metadata_json: \"{}\", cells: [{cell_type: \"raw\", metadata_json: \"{}\", source: \"\", has_execution_count: false, execution_count: -1, outputs: []}]}")
match parsed:
    case Ok(_):
        fail("expected an Err for cell_type 'raw'")
    case Err(msg):
        expect(msg).to_contain("cell_type")
```

</details>

### ipynb <-> snb.sdn lossless conversion

#### round-trips .ipynb -> .snb.sdn -> .ipynb byte-stable for the supported subset

- round-trips .ipynb -> .snb.sdn -> .ipynb byte-stable for the supported subset
   - Expected: ipynb_text2 equals `ipynb_text1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round-trips .ipynb -> .snb.sdn -> .ipynb byte-stable for the supported subset")
val nb = make_hello_notebook()
val ipynb_text1 = ipynb_serialize(nb)

val nb2_result = ipynb_parse(ipynb_text1)
var nb2 = nb
match nb2_result:
    case Ok(v):
        nb2 = v
    case Err(msg):
        fail("expected ipynb_parse to succeed, got error: {msg}")

val snb_text = snb_serialize(nb2)

val nb3_result = snb_parse(snb_text)
var nb3 = nb
match nb3_result:
    case Ok(v):
        nb3 = v
    case Err(msg):
        fail("expected snb_parse to succeed, got error: {msg}")

val ipynb_text2 = ipynb_serialize(nb3)
expect(ipynb_text2).to_equal(ipynb_text1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/notebook/snb_sdn_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering snb_serialize / snb_parse, ipynb <-> snb.sdn lossless conversion.
- snb_serialize / snb_parse
- ipynb <-> snb.sdn lossless conversion

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `84e6e5f849b3728017624f6733b0e1bd78ee25ce41d3bbf59000cc502b2b0777`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `84e6e5f849b3728017624f6733b0e1bd78ee25ce41d3bbf59000cc502b2b0777`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `84e6e5f849b3728017624f6733b0e1bd78ee25ce41d3bbf59000cc502b2b0777`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/nogc_sync_mut/notebook/snb_sdn_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/notebook/snb_sdn_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/notebook/snb_sdn_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/notebook/snb_sdn_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/notebook/snb_sdn_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/notebook/snb_sdn_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips a notebook through SDN text unchanged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/notebook/snb_sdn_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves cell content through the SDN round trip' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/notebook/snb_sdn_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails fast on an unsupported cell_type in SDN' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
