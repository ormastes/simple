# Claude Full side question utils

> Pure Simple coverage for /btw trigger detection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full side question utils

Pure Simple coverage for /btw trigger detection.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/side_question_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for /btw trigger detection.

## Scenarios

### Claude full side question utils

#### finds btw trigger at the start of input

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- finds btw trigger at the start of input
- Check trigger position
   - Expected: positions.len() equals `1`
   - Expected: positions[0].word equals `/btw`
   - Expected: positions[0].start equals `0`
   - Expected: positions[0].end equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("finds btw trigger at the start of input")
step("Check trigger position")
val positions = findBtwTriggerPositions("/btw what changed?")
expect(positions.len()).to_equal(1)
expect(positions[0].word).to_equal("/btw")
expect(positions[0].start).to_equal(0)
expect(positions[0].end).to_equal(4)
```

</details>

#### matches the trigger case-insensitively

- matches the trigger case-insensitively
- Check case-insensitive match
   - Expected: positions.len() equals `1`
   - Expected: positions[0].word equals `/BTW`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches the trigger case-insensitively")
step("Check case-insensitive match")
val positions = findBtwTriggerPositions("/BTW now")
expect(positions.len()).to_equal(1)
expect(positions[0].word).to_equal("/BTW")
```

</details>

#### requires the trigger at index zero

- requires the trigger at index zero
- Check start anchor
   - Expected: findBtwTriggerPositions(" /btw later").len() equals `0`
   - Expected: findBtwTriggerPositions("ask /btw later").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires the trigger at index zero")
step("Check start anchor")
expect(findBtwTriggerPositions(" /btw later").len()).to_equal(0)
expect(findBtwTriggerPositions("ask /btw later").len()).to_equal(0)
```

</details>

#### requires a word boundary after btw

- requires a word boundary after btw
- Check word boundary
   - Expected: findBtwTriggerPositions("/btw").len() equals `1`
   - Expected: findBtwTriggerPositions("/btw?").len() equals `1`
   - Expected: findBtwTriggerPositions("/btw_later").len() equals `0`
   - Expected: findBtwTriggerPositions("/btwice").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires a word boundary after btw")
step("Check word boundary")
expect(findBtwTriggerPositions("/btw").len()).to_equal(1)
expect(findBtwTriggerPositions("/btw?").len()).to_equal(1)
expect(findBtwTriggerPositions("/btw_later").len()).to_equal(0)
expect(findBtwTriggerPositions("/btwice").len()).to_equal(0)
```

</details>

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f12f93d190da48aeeae25979dd3ac8c892c288a6e8e014e785775cc59bd83039`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f12f93d190da48aeeae25979dd3ac8c892c288a6e8e014e785775cc59bd83039`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f12f93d190da48aeeae25979dd3ac8c892c288a6e8e014e785775cc59bd83039`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/utils/side_question_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/side_question_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/side_question_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/side_question_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/side_question_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/side_question_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds btw trigger at the start of input' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/side_question_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the trigger case-insensitively' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/side_question_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires the trigger at index zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
