# Query Json Payload Specification

> Tests covering LSP query JSON payload extraction.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Query Json Payload Specification

## Scenarios

### LSP query JSON payload extraction

#### keeps completion JSON after bootstrap stdout diagnostics

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps completion JSON after bootstrap stdout diagnostics
   - Expected: lsp_extract_query_json_payload(output) equals `[{"label":"my_completable_function","kind":6}]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps completion JSON after bootstrap stdout diagnostics")
val output = "WARNING: bootstrap seed\nwarning: deprecated syntax\n[{\"label\":\"my_completable_function\",\"kind\":6}]\n"
expect(lsp_extract_query_json_payload(output)).to_equal("[{\"label\":\"my_completable_function\",\"kind\":6}]")
```

</details>

#### keeps hover JSON after bootstrap stdout diagnostics

- keeps hover JSON after bootstrap stdout diagnostics
   - Expected: lsp_extract_query_json_payload(output) equals `{"contents":{"kind":"markdown","value":"fn item"}}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps hover JSON after bootstrap stdout diagnostics")
val output = "WARNING: bootstrap seed\n{\"contents\":{\"kind\":\"markdown\",\"value\":\"fn item\"}}\n"
expect(lsp_extract_query_json_payload(output)).to_equal("{\"contents\":{\"kind\":\"markdown\",\"value\":\"fn item\"}}")
```

</details>

<details>
<summary>Advanced: fails closed when diagnostics contain no JSON payload</summary>

#### fails closed when diagnostics contain no JSON payload

- fails closed when diagnostics contain no JSON payload
   - Expected: lsp_extract_query_json_payload("WARNING: bootstrap seed\nwarning: no payload\n") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed when diagnostics contain no JSON payload")
expect(lsp_extract_query_json_payload("WARNING: bootstrap seed\nwarning: no payload\n")).to_equal("")
```

</details>


</details>

#### uses the last complete payload after stale diagnostic JSON

- uses the last complete payload after stale diagnostic JSON
   - Expected: lsp_extract_query_json_payload(output) equals `[{"label":"fresh"}]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses the last complete payload after stale diagnostic JSON")
val output = "{\"diagnostic\":true}\n[{\"label\":\"fresh\"}]\n"
expect(lsp_extract_query_json_payload(output)).to_equal("[{\"label\":\"fresh\"}]")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/lsp/query_json_payload_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering LSP query JSON payload extraction.
- LSP query JSON payload extraction

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1f5348d370098330865b12d8e1c6f37164b34b5fd969f06f046a6765308c6890`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1f5348d370098330865b12d8e1c6f37164b34b5fd969f06f046a6765308c6890`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1f5348d370098330865b12d8e1c6f37164b34b5fd969f06f046a6765308c6890`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/lsp/query_json_payload_spec.spl
mirror: doc/06_spec/01_unit/app/lsp/query_json_payload_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/lsp/query_json_payload_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/lsp/query_json_payload_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/lsp/query_json_payload_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps completion JSON after bootstrap stdout diagnostics' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/lsp/query_json_payload_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps hover JSON after bootstrap stdout diagnostics' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/lsp/query_json_payload_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed when diagnostics contain no JSON payload' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
