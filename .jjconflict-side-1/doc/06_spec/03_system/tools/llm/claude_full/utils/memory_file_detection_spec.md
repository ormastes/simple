# Claude Full memory file detection

> Pure Simple coverage for session pattern classification.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full memory file detection

Pure Simple coverage for session pattern classification.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/memory_file_detection_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for session pattern classification.

## Scenarios

### Claude full memory file detection

#### detects session memory patterns

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- detects session memory patterns
- Check memory markdown and wildcard patterns
   - Expected: detectSessionPatternType("session-memory/current.md") equals `Some("session_memory")`
   - Expected: detectSessionPatternType("session-memory/*") equals `Some("session_memory")`
   - Expected: detectSessionPatternType("session-memory\\current.md") equals `Some("session_memory")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects session memory patterns")
step("Check memory markdown and wildcard patterns")
expect(detectSessionPatternType("session-memory/current.md")).to_equal(Some("session_memory"))
expect(detectSessionPatternType("session-memory/*")).to_equal(Some("session_memory"))
expect(detectSessionPatternType("session-memory\\current.md")).to_equal(Some("session_memory"))
```

</details>

#### detects session transcript patterns

- detects session transcript patterns
- Check jsonl and projects glob patterns
   - Expected: detectSessionPatternType("projects/foo/session.jsonl") equals `Some("session_transcript")`
   - Expected: detectSessionPatternType("projects/*/*.jsonl") equals `Some("session_transcript")`
   - Expected: detectSessionPatternType("logs/output.jsonl") equals `Some("session_transcript")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects session transcript patterns")
step("Check jsonl and projects glob patterns")
expect(detectSessionPatternType("projects/foo/session.jsonl")).to_equal(Some("session_transcript"))
expect(detectSessionPatternType("projects/*/*.jsonl")).to_equal(Some("session_transcript"))
expect(detectSessionPatternType("logs/output.jsonl")).to_equal(Some("session_transcript"))
```

</details>

#### returns nil for unrelated patterns

- returns nil for unrelated patterns
- Check non-session patterns


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns nil for unrelated patterns")
step("Check non-session patterns")
expect(detectSessionPatternType("session-memory/current.txt")).to_be_nil()
expect(detectSessionPatternType("projects/foo/session.json")).to_be_nil()
expect(detectSessionPatternType("README.md")).to_be_nil()
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

- Canonical SPipe generation for source `b6a8557f0c2d779e6d6fae129673dfa72c806754f5cca4a84bd6cc6431625b87`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b6a8557f0c2d779e6d6fae129673dfa72c806754f5cca4a84bd6cc6431625b87`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b6a8557f0c2d779e6d6fae129673dfa72c806754f5cca4a84bd6cc6431625b87`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/llm/claude_full/utils/memory_file_detection_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/memory_file_detection_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/memory_file_detection_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/memory_file_detection_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/memory_file_detection_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects session memory patterns' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/memory_file_detection_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects session transcript patterns' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/memory_file_detection_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns nil for unrelated patterns' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
