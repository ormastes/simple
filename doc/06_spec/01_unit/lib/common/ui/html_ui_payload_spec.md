# Html Ui Payload Specification

> Tests covering html ui payload helpers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Html Ui Payload Specification

## Scenarios

### html ui payload helpers

#### round trips ASCII payloads through base64

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- round trips ASCII payloads through base64
   - Expected: encoded equals `aGVsbG8=`
   - Expected: payload_decode(encoded) equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round trips ASCII payloads through base64")
val encoded = payload_encode("hello")
expect(encoded).to_equal("aGVsbG8=")
expect(payload_decode(encoded)).to_equal("hello")
```

</details>

#### splits payloads without changing chunk order

- splits payloads without changing chunk order
   - Expected: chunks.len() equals `3`
   - Expected: chunks[0] equals `abcde`
   - Expected: chunks[1] equals `fghij`
   - Expected: chunks[2] equals `kl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("splits payloads without changing chunk order")
val chunks = payload_split("abcdefghijkl", 5)
expect(chunks.len()).to_equal(3)
expect(chunks[0]).to_equal("abcde")
expect(chunks[1]).to_equal("fghij")
expect(chunks[2]).to_equal("kl")
```

</details>

#### generates std module source with embedded html and css payloads

- generates std module source with embedded html and css payloads


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("generates std module source with embedded html and css payloads")
val src = gen_std_module_source("page", "HTML", ["CSS"])
expect(src).to_contain("# Generated std UI module: page")
expect(src).to_contain("fn ui_html_b64() -> text:")
expect(src).to_contain("    \"HTML\"")
expect(src).to_contain("fn ui_css_b64(idx: i64) -> text:")
expect(src).to_contain("    if idx == 0:")
expect(src).to_contain("        \"CSS\"")
expect(src).to_contain("export ui_css_b64")
```

</details>

#### generates dyn main source with part lookup

- generates dyn main source with part lookup


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("generates dyn main source with part lookup")
val map = UiPartMap(tags: ["button", "input"], parts: ["page_part_0.smf", "page_part_1.smf"])
val src = gen_dyn_main_source("page", map, "", [])
expect(src).to_contain("# Generated dyn main UI module: page")
expect(src).to_contain("\"button\",")
expect(src).to_contain("\"input\"")
expect(src).to_contain("fn ui_part_for(tag: text) -> text:")
expect(src).to_contain("    if tag == \"button\":")
expect(src).to_contain("        \"page_part_0.smf\"")
expect(src).to_contain("    else if tag == \"input\":")
expect(src).to_contain("        \"page_part_1.smf\"")
expect(src).to_contain("export ui_part_for")
```

</details>

#### generates dyn part source with the payload literal

- generates dyn part source with the payload literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("generates dyn part source with the payload literal")
val src = gen_dyn_part_source("page", 2, "PAYLOAD")
expect(src).to_contain("# Generated dyn part module: page_part_2")
expect(src).to_contain("fn ui_part_payload() -> text:")
expect(src).to_contain("    \"PAYLOAD\"")
expect(src).to_contain("export ui_part_payload")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/html_ui_payload_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering html ui payload helpers.
- html ui payload helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `5004277cc632d092fc1757eb48fa2ed334599ebe08462101222c8c6eaed23f89`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5004277cc632d092fc1757eb48fa2ed334599ebe08462101222c8c6eaed23f89`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5004277cc632d092fc1757eb48fa2ed334599ebe08462101222c8c6eaed23f89`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/common/ui/html_ui_payload_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/html_ui_payload_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/html_ui_payload_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/html_ui_payload_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/html_ui_payload_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/ui/html_ui_payload_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round trips ASCII payloads through base64' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/html_ui_payload_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'splits payloads without changing chunk order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/html_ui_payload_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates std module source with embedded html and css payloads' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
