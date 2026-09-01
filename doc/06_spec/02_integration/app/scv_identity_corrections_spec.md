# scv_identity_corrections_spec

> Purpose: This spec proves SCV-IMPL-I-06 — identity corrections as LOGGED

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_identity_corrections_spec

Purpose: This spec proves SCV-IMPL-I-06 — identity corrections as LOGGED

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/scv_identity_corrections_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves SCV-IMPL-I-06 — identity corrections as LOGGED
operations: `scv identity link|unlink|split|merge|trace`. Every correction
appends a row to .scv/meta/identity_corrections.sdn (append-only) plus an
identity edge with `correction:<op>:<seq>` evidence; superseded evidence is
ALIASED by reference (`edge:<n>`), never rewritten. Terminal states mirror
delete-is-terminal: split -> state=split, merge loser -> state=merged; a
terminal id refuses further corrections and its id is never reused. `trace`
overlays row + edge history + corrections.
Audience: Maintainers of the SCV identity/corrections path.

## Scenarios

### scv identity corrections (SCV-IMPL-I-06)

#### logs unlink+link as appended corrections aliasing superseded edges

**Manual warnings:**
- invalid manual visibility metadata: # @manual SCV commit gates (expected show, folded, detail, or skip)


- Snapshot a.txt, unlink it, link its id to b.txt, trace
- Verify logged PASS verdicts, alias references, and append-only log rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-IDENTITY-CORRECTIONS-001
# @req REQ-SSPEC-INTEGRATION
step("Snapshot a.txt, unlink it, link its id to b.txt, trace")
var lines = _prelude("linkun")
lines.push("scv identity unlink a.txt wrong-match")
lines.push("scv identity link file_1 b.txt actually-moved")
lines.push("scv identity trace file_1")
lines.push("echo '=== corrections log ==='")
lines.push("cat .scv/meta/identity_corrections.sdn")
val out = _run(lines)
step("Verify logged PASS verdicts, alias references, and append-only log rows")
expect(out).to_contain("PASS — identity unlink recorded: seq=1 file_1 detached from a.txt (supersedes edge:")
expect(out).to_contain("PASS — identity link recorded: seq=2 file_1 -> b.txt (supersedes edge:")
expect(out).to_contain("current_path: b.txt")
expect(out).to_contain("seq=1 op=unlink args=a.txt,file_1 supersedes=edge:")
expect(out).to_contain("seq=2 op=link args=file_1,b.txt supersedes=edge:")
expect(out).to_contain("1|unlink|a.txt|file_1|")
expect(out).to_contain("2|link|file_1|b.txt|")
expect(out).to_contain("exit=0")
```

</details>

#### split and merge are terminal, id-preserving, and refused on terminal ids

- Split file_1 into two ids, merge them, then try correcting terminals
- Verify terminal states, refusal on terminal id, edges appended not rewritten


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-IDENTITY-CORRECTIONS-001
step("Split file_1 into two ids, merge them, then try correcting terminals")
var lines = _prelude("splitmg")
lines.push("scv identity split file_1 c1.txt c2.txt two-files")
lines.push("scv identity merge file_2 file_3 same-file || true")
lines.push("scv identity link file_1 z.txt late || echo refused-link-rc=$?")
lines.push("scv identity trace file_1")
lines.push("scv identity trace file_3")
lines.push("echo '=== rows ==='")
lines.push("cat .scv/meta/file_identity.sdn")
val out = _run(lines)
step("Verify terminal states, refusal on terminal id, edges appended not rewritten")
expect(out).to_contain("PASS — identity split recorded: seq=1 file_1 -> file_2(c1.txt) + file_3(c2.txt); file_1 terminal (state=split)")
expect(out).to_contain("PASS — identity merge recorded: seq=2 file_3 merged into file_2; file_3 terminal (state=merged)")
expect(out).to_contain("FAIL — identity link refused: file_1 is terminal (state=split)")
expect(out).to_contain("refused-link-rc=1")
expect(out).to_contain("state: split")
expect(out).to_contain("state: merged")
# rows file keeps the terminal ids (never deleted, never reused):
expect(out).to_contain("|split")
expect(out).to_contain("|merged")
expect(out).to_contain("exit=0")
```

</details>

#### trace on an unknown id is a fail-closed ERROR, and the edge log is append-only across corrections

- Record one correction, capture the edge log, record another, re-capture
- Verify old edge bytes are a byte-identical prefix and unknown id is ERROR rc=2


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-IDENTITY-CORRECTIONS-001
step("Record one correction, capture the edge log, record another, re-capture")
var lines = _prelude("appendonly")
lines.push("scv identity unlink a.txt first >/dev/null")
lines.push("cp .scv/meta/identity_edges.sdn /tmp/edges-before-$$")
lines.push("scv identity link file_1 b.txt second >/dev/null")
lines.push("head -c $(wc -c < /tmp/edges-before-$$) .scv/meta/identity_edges.sdn > /tmp/edges-prefix-$$")
lines.push("cmp -s /tmp/edges-before-$$ /tmp/edges-prefix-$$ && echo PREFIX-PRESERVED")
lines.push("rm -f /tmp/edges-before-$$ /tmp/edges-prefix-$$")
lines.push("scv identity trace file_99 || echo trace-rc=$?")
val out = _run(lines)
step("Verify old edge bytes are a byte-identical prefix and unknown id is ERROR rc=2")
expect(out).to_contain("PREFIX-PRESERVED")
expect(out).to_contain("ERROR — nothing was checked (unknown file id: file_99)")
expect(out).to_contain("trace-rc=2")
expect(out).to_contain("exit=0")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-SCV-IDENTITY-CORRECTIONS-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `85089cc43a58dcb03432f4b80511b77d477bc7923304f6a4e59d496a0cb8fbd4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `85089cc43a58dcb03432f4b80511b77d477bc7923304f6a4e59d496a0cb8fbd4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `85089cc43a58dcb03432f4b80511b77d477bc7923304f6a4e59d496a0cb8fbd4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/02_integration/app/scv_identity_corrections_spec.spl
mirror: doc/06_spec/02_integration/app/scv_identity_corrections_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/scv_identity_corrections_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/scv_identity_corrections_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/app/scv_identity_corrections_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'logs unlink+link as appended corrections aliasing superseded edges' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/scv_identity_corrections_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'split and merge are terminal, id-preserving, and refused on terminal ids' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/scv_identity_corrections_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'trace on an unknown id is a fail-closed ERROR, and the edge log is append-only across corrections' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
