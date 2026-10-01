# Claude Full CLI NDJSON Safe Stringify

> Checks escaping for JavaScript line terminators in one-line JSON output.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full CLI NDJSON Safe Stringify

Checks escaping for JavaScript line terminators in one-line JSON output.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/cli/ndjsonSafeStringify_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks escaping for JavaScript line terminators in one-line JSON output.

## Scenarios

### Claude full cli ndjson safe stringify

#### escapes JavaScript line terminators

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- escapes JavaScript line terminators
- Line and paragraph separators become slash-u escapes
   - Expected: escaped equals `{"text":"a\\u2028b\\u2029c"}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("escapes JavaScript line terminators")
step("Line and paragraph separators become slash-u escapes")
val json = "{\"text\":\"a" + lineSeparatorChar() + "b" + paragraphSeparatorChar() + "c\"}"
val escaped = ndjsonSafeStringify(json)
expect(escaped).to_equal("{\"text\":\"a\\u2028b\\u2029c\"}")
```

</details>

#### leaves ordinary JSON unchanged

- leaves ordinary JSON unchanged
- Normal one-line JSON remains stable
   - Expected: escapeJsLineTerminators("{\"ok\":true}") equals `{"ok":true}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("leaves ordinary JSON unchanged")
step("Normal one-line JSON remains stable")
expect(escapeJsLineTerminators("{\"ok\":true}")).to_equal("{\"ok\":true}")
```

</details>

#### exports source-backed constants

- exports source-backed constants
- Pin the transport-safety contract
   - Expected: escapedLineSeparator() equals `\\u2028`
   - Expected: escapedParagraphSeparator() equals `\\u2029`
   - Expected: jsLineTerminatorsPattern() equals `\\u2028|\\u2029`
   - Expected: usesSingleAlternationRegexInSource() is true
   - Expected: preservesJsonParseValue() is true
   - Expected: protectsOneMessagePerLineTransports() is true
   - Expected: ndjsonSafeStringifySourceLinesModeled() equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exports source-backed constants")
step("Pin the transport-safety contract")
expect(escapedLineSeparator()).to_equal("\\u2028")
expect(escapedParagraphSeparator()).to_equal("\\u2029")
expect(jsLineTerminatorsPattern()).to_equal("\\u2028|\\u2029")
expect(usesSingleAlternationRegexInSource()).to_equal(true)
expect(preservesJsonParseValue()).to_equal(true)
expect(protectsOneMessagePerLineTransports()).to_equal(true)
expect(ndjsonSafeStringifySourceLinesModeled()).to_equal(32)
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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d4769c1a2346960651806a83a591c76534eb83aab44280f867f6b319d09ccfda`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d4769c1a2346960651806a83a591c76534eb83aab44280f867f6b319d09ccfda`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d4769c1a2346960651806a83a591c76534eb83aab44280f867f6b319d09ccfda`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/tools/llm/claude_full/cli/ndjsonSafeStringify_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/cli/ndjsonSafeStringify_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/cli/ndjsonSafeStringify_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/cli/ndjsonSafeStringify_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/cli/ndjsonSafeStringify_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/cli/ndjsonSafeStringify_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'escapes JavaScript line terminators' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/cli/ndjsonSafeStringify_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leaves ordinary JSON unchanged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/cli/ndjsonSafeStringify_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exports source-backed constants' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
