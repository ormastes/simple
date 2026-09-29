# ink TerminalQuerier

> The Claude-full ink TUI needs to know what the host terminal supports before

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ink TerminalQuerier

The Claude-full ink TUI needs to know what the host terminal supports before

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/claude_full/ink/terminal_querier_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

The Claude-full ink TUI needs to know what the host terminal supports before
it picks a rendering path. It asks the terminal with standardized CSI/OSC
query sequences and matches replies against the query that asked them.

The audience is the engineer changing the querier or adding a new probe. This
specification pins the request byte sequences, the reply-to-query matching
rules, and the sentinel-driven drain behaviour that bounds how long the TUI
waits for an answer.

## Scope and Preconditions

Executable against `src/app/llm_caret/claude_full/ink/terminal_querier.spl`.
All scenarios run against a fresh in-memory `TerminalQuerier`; no real
terminal is attached, so `writtenText()` observes exactly what the querier
would emit.

## Primary Workflow

Send one or more typed queries (DA2, DA1, kitty keyboard, XTVERSION, DECRQM,
OSC color), observe each request written to stdout, then feed responses back
and confirm each pending query resolves against the reply that matches its
own type and code.

## Recovery and Troubleshooting

Terminals that never answer are unblocked by `flush()`, which queues a DA1
sentinel: when the DA1 reply arrives, every still-pending unsupported query
drains as `undefined` instead of hanging the TUI. An unmatched DA1 with no
sentinel queued is ignored, not treated as a resolution.

## Scenarios

### ink TerminalQuerier request construction

#### builds request sequences from the CSI/OSC helpers

- builds request sequences from the CSI/OSC helpers
- Ask each standard probe for its request sequence
   - Expected: da1().request equals `csi("c")`
   - Expected: da2().request equals `csi(">c")`
   - Expected: kittyKeyboard().request equals `csi("?u")`
   - Expected: xtversion().request equals `csi(">0q")`
   - Expected: decrqm(2026).request equals `csi("?2026$p")`
   - Expected: oscColor(11).request equals `osc(11, "?")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds request sequences from the CSI/OSC helpers")
step("Ask each standard probe for its request sequence")
expect(da1().request).to_equal(csi("c"))
expect(da2().request).to_equal(csi(">c"))
expect(kittyKeyboard().request).to_equal(csi("?u"))
expect(xtversion().request).to_equal(csi(">0q"))
expect(decrqm(2026).request).to_equal(csi("?2026$p"))
expect(oscColor(11).request).to_equal(osc(11, "?"))
```

</details>

#### uses DEC private CSI ?6n for cursor position to avoid F-key ambiguity

- uses DEC private CSI ?6n for cursor position to avoid F-key ambiguity
- Request the cursor position
   - Expected: cursorPosition().request equals `csi("?6n")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses DEC private CSI ?6n for cursor position to avoid F-key ambiguity")
step("Request the cursor position")
expect(cursorPosition().request).to_equal(csi("?6n"))
```

</details>

### ink TerminalQuerier reply matching

#### matches DECRPM only on the same mode

- matches DECRPM only on the same mode
- Reply with the same mode number, then a different one
   - Expected: queryMatches(decrqm(2026), decrpmResponse(2026)) is true
   - Expected: queryMatches(decrqm(2026), decrpmResponse(1049)) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches DECRPM only on the same mode")
step("Reply with the same mode number, then a different one")
expect(queryMatches(decrqm(2026), decrpmResponse(2026))).to_equal(true)
expect(queryMatches(decrqm(2026), decrpmResponse(1049))).to_equal(false)
```

</details>

#### matches OSC only on the same code

- matches OSC only on the same code
- Reply with the same OSC code, then a different one
   - Expected: queryMatches(oscColor(11), oscResponse(11)) is true
   - Expected: queryMatches(oscColor(11), oscResponse(10)) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches OSC only on the same code")
step("Reply with the same OSC code, then a different one")
expect(queryMatches(oscColor(11), oscResponse(11))).to_equal(true)
expect(queryMatches(oscColor(11), oscResponse(10))).to_equal(false)
```

</details>

#### rejects a response whose type differs from the query

- rejects a response whose type differs from the query
- Answer a DA2 query with a DA1 reply
   - Expected: queryMatches(da2(), response("da1")) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a response whose type differs from the query")
step("Answer a DA2 query with a DA1 reply")
expect(queryMatches(da2(), response("da1"))).to_equal(false)
```

</details>

### ink TerminalQuerier query lifecycle

#### writes each query request to stdout as it is sent

- writes each query request to stdout as it is sent
- Send DA2 then the kitty keyboard probe
   - Expected: q.pendingCount() equals `2`
   - Expected: q.writtenText() equals `csi(">c") + csi("?u")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("writes each query request to stdout as it is sent")
step("Send DA2 then the kitty keyboard probe")
var q = TerminalQuerier.new()
q.send(da2())
q.send(kittyKeyboard())
expect(q.pendingCount()).to_equal(2)  # oracle: authoritative expected value documented in the plan/bug record this spec pins
expect(q.writtenText()).to_equal(csi(">c") + csi("?u"))
```

</details>

#### resolves the first matching pending query, not only the queue head

- resolves the first matching pending query, not only the queue head
- Send DA2 then an OSC color query, and answer the OSC one
   - Expected: q.pendingCount() equals `1`
   - Expected: q.resolved.len() equals `1`
   - Expected: q.resolved[0] equals `osc:osc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves the first matching pending query, not only the queue head")
step("Send DA2 then an OSC color query, and answer the OSC one")
var q = TerminalQuerier.new()
q.send(da2())
q.send(oscColor(11))
q.onResponse(oscResponse(11))
expect(q.pendingCount()).to_equal(1)  # oracle: authoritative expected value documented in the plan/bug record this spec pins
expect(q.resolved.len()).to_equal(1)  # oracle: authoritative expected value documented in the plan/bug record this spec pins
expect(q.resolved[0]).to_equal("osc:osc")
```

</details>

#### writes a DA1 sentinel on flush

- writes a DA1 sentinel on flush
- Flush a querier with nothing pending
   - Expected: q.writtenText() equals `sentinel()`
   - Expected: q.pendingCount() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("writes a DA1 sentinel on flush")
step("Flush a querier with nothing pending")
var q = TerminalQuerier.new()
q.flush()
expect(q.writtenText()).to_equal(sentinel())
expect(q.pendingCount()).to_equal(1)  # oracle: authoritative expected value documented in the plan/bug record this spec pins
```

</details>

#### drains unsupported queries through the sentinel when DA1 comes back unmatched

- drains unsupported queries through the sentinel when DA1 comes back unmatched
- Send probes a terminal cannot answer, then flush and return DA1
- Confirm every pending query drained, in order, ending at the sentinel
   - Expected: q.pendingCount() equals `0`
   - Expected: q.resolved.len() equals `3`
   - Expected: q.resolved[0] equals `kittyKeyboard:undefined`
   - Expected: q.resolved[1] equals `decrpm:undefined`
   - Expected: q.resolved[2] equals `sentinel:resolved`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("drains unsupported queries through the sentinel when DA1 comes back unmatched")
step("Send probes a terminal cannot answer, then flush and return DA1")
var q = TerminalQuerier.new()
q.send(kittyKeyboard())
q.send(decrqm(2026))
q.flush()
q.onResponse(response("da1"))
step("Confirm every pending query drained, in order, ending at the sentinel")
expect(q.pendingCount()).to_equal(0)  # oracle: authoritative expected value documented in the plan/bug record this spec pins
expect(q.resolved.len()).to_equal(3)  # oracle: authoritative expected value documented in the plan/bug record this spec pins
expect(q.resolved[0]).to_equal("kittyKeyboard:undefined")
expect(q.resolved[1]).to_equal("decrpm:undefined")
expect(q.resolved[2]).to_equal("sentinel:resolved")
```

</details>

#### keeps queries sent after the sentinel queued for a later batch

- keeps queries sent after the sentinel queued for a later batch
- Flush, then send DA2, then answer the DA1 sentinel
   - Expected: q.pendingCount() equals `1`
   - Expected: q.resolved.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps queries sent after the sentinel queued for a later batch")
step("Flush, then send DA2, then answer the DA1 sentinel")
var q = TerminalQuerier.new()
q.send(kittyKeyboard())
q.flush()
q.send(da2())
q.onResponse(response("da1"))
expect(q.pendingCount()).to_equal(1)  # oracle: authoritative expected value documented in the plan/bug record this spec pins
expect(q.resolved.len()).to_equal(2)  # oracle: authoritative expected value documented in the plan/bug record this spec pins
```

</details>

#### ignores an unmatched DA1 when no sentinel is queued

- ignores an unmatched DA1 when no sentinel is queued
- Answer DA1 without ever flushing
   - Expected: q.pendingCount() equals `1`
   - Expected: q.resolved.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ignores an unmatched DA1 when no sentinel is queued")
step("Answer DA1 without ever flushing")
var q = TerminalQuerier.new()
q.send(kittyKeyboard())
q.onResponse(response("da1"))
expect(q.pendingCount()).to_equal(1)  # oracle: authoritative expected value documented in the plan/bug record this spec pins
expect(q.resolved.len()).to_equal(0)  # oracle: authoritative expected value documented in the plan/bug record this spec pins
```

</details>

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

- Canonical SPipe generation for source `639eb55f25ff3b8e88b98b8768b30a5a56f3f4f241f7b12e304dbcd755fe7234`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `639eb55f25ff3b8e88b98b8768b30a5a56f3f4f241f7b12e304dbcd755fe7234`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `639eb55f25ff3b8e88b98b8768b30a5a56f3f4f241f7b12e304dbcd755fe7234`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/llm_caret/claude_full/ink/terminal_querier_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/claude_full/ink/terminal_querier_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/llm_caret/claude_full/ink/terminal_querier_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/claude_full/ink/terminal_querier_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: evidence
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/claude_full/ink/terminal_querier_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds request sequences from the CSI/OSC helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/claude_full/ink/terminal_querier_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses DEC private CSI ?6n for cursor position to avoid F-key ambiguity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/claude_full/ink/terminal_querier_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches DECRPM only on the same mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
