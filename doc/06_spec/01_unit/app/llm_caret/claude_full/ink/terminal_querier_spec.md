# Terminal Querier Specification

> Tests covering ink TerminalQuerier.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Terminal Querier Specification

## Scenarios

### ink TerminalQuerier

#### builds request sequences from the CSI/OSC helpers
#### uses DEC private CSI ?6n for cursor position to avoid F-key ambiguity

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cursorPosition().request).to_equal(csi("?6n"))
```

</details>

#### matches DECRPM only on the same mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(queryMatches(decrqm(2026), decrpmResponse(2026))).to_equal(true)
expect(queryMatches(decrqm(2026), decrpmResponse(1049))).to_equal(false)
```

</details>

#### matches OSC only on the same code

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(queryMatches(oscColor(11), oscResponse(11))).to_equal(true)
expect(queryMatches(oscColor(11), oscResponse(10))).to_equal(false)
```

</details>

#### rejects a response whose type differs from the query

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(queryMatches(da2(), response("da1"))).to_equal(false)
```

</details>

#### writes each query request to stdout as it is sent

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = TerminalQuerier.new()
q.send(da2())
q.send(kittyKeyboard())
expect(q.pendingCount()).to_equal(2)
expect(q.writtenText()).to_equal(csi(">c") + csi("?u"))
```

</details>

#### resolves the first matching pending query, not only the queue head

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = TerminalQuerier.new()
q.send(da2())
q.send(oscColor(11))
q.onResponse(oscResponse(11))
expect(q.pendingCount()).to_equal(1)
expect(q.resolved.len()).to_equal(1)
expect(q.resolved[0]).to_equal("osc:osc")
```

</details>

#### writes a DA1 sentinel on flush

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = TerminalQuerier.new()
q.flush()
expect(q.writtenText()).to_equal(sentinel())
expect(q.pendingCount()).to_equal(1)
```

</details>

#### drains unsupported queries through the sentinel when DA1 comes back unmatched

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = TerminalQuerier.new()
q.send(kittyKeyboard())
q.send(decrqm(2026))
q.flush()
q.onResponse(response("da1"))
expect(q.pendingCount()).to_equal(0)
expect(q.resolved.len()).to_equal(3)
expect(q.resolved[0]).to_equal("kittyKeyboard:undefined")
expect(q.resolved[1]).to_equal("decrpm:undefined")
expect(q.resolved[2]).to_equal("sentinel:resolved")
```

</details>

#### keeps queries sent after the sentinel queued for a later batch

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = TerminalQuerier.new()
q.send(kittyKeyboard())
q.flush()
q.send(da2())
q.onResponse(response("da1"))
expect(q.pendingCount()).to_equal(1)
expect(q.resolved.len()).to_equal(2)
```

</details>

#### ignores an unmatched DA1 when no sentinel is queued

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = TerminalQuerier.new()
q.send(kittyKeyboard())
q.onResponse(response("da1"))
expect(q.pendingCount()).to_equal(1)
expect(q.resolved.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/claude_full/ink/terminal_querier_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ink TerminalQuerier.
- ink TerminalQuerier

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `cec0a73b0fa0786d5679c6286201b4cc593f6925858610e7fd635cfb100ca8c3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cec0a73b0fa0786d5679c6286201b4cc593f6925858610e7fd635cfb100ca8c3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cec0a73b0fa0786d5679c6286201b4cc593f6925858610e7fd635cfb100ca8c3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **77/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/llm_caret/claude_full/ink/terminal_querier_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/claude_full/ink/terminal_querier_spec.md (current)
findings: 9 blockers: 1
  narrative=100 structure=60 oracle=70
  traceability=60 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=77; blocker cap makes effective=49
doc/06_spec/01_unit/app/llm_caret/claude_full/ink/terminal_querier_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/claude_full/ink/terminal_querier_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/claude_full/ink/terminal_querier_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/app/llm_caret/claude_full/ink/terminal_querier_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/llm_caret/claude_full/ink/terminal_querier_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/llm_caret/claude_full/ink/terminal_querier_spec.spl:17:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'builds request sequences from the CSI/OSC helpers' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/app/llm_caret/claude_full/ink/terminal_querier_spec.spl:28:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'uses DEC private CSI ?6n for cursor position to avoid F-key ambiguity' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/app/llm_caret/claude_full/ink/terminal_querier_spec.spl:32:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'matches DECRPM only on the same mode' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/app/llm_caret/claude_full/ink/terminal_querier_spec.spl:37:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'matches OSC only on the same code' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
