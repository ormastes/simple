# Claude Full user agent utils

> Pure Simple coverage for Claude Code User-Agent formatting.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full user agent utils

Pure Simple coverage for Claude Code User-Agent formatting.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/userAgent_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for Claude Code User-Agent formatting.

## Scenarios

### Claude full user agent utils

#### formats the versioned Claude Code user agent

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- formats the versioned Claude Code user agent
- Check user-agent format
   - Expected: getClaudeCodeUserAgent("1.2.3") equals `claude-code/1.2.3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("formats the versioned Claude Code user agent")
step("Check user-agent format")
expect(getClaudeCodeUserAgent("1.2.3")).to_equal("claude-code/1.2.3")
```

</details>

#### keeps the helper dependency-free and literal

- keeps the helper dependency-free and literal
- Check no trimming or normalization
   - Expected: getClaudeCodeUserAgent(" dev ") equals `claude-code/ dev `


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps the helper dependency-free and literal")
step("Check no trimming or normalization")
expect(getClaudeCodeUserAgent(" dev ")).to_equal("claude-code/ dev ")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `747182bf028a04eee7ecf78869e9e387d947050978147aebdae517adc10b1a94`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `747182bf028a04eee7ecf78869e9e387d947050978147aebdae517adc10b1a94`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `747182bf028a04eee7ecf78869e9e387d947050978147aebdae517adc10b1a94`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/tools/llm/claude_full/utils/userAgent_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/userAgent_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/userAgent_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/userAgent_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/userAgent_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats the versioned Claude Code user agent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/userAgent_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the helper dependency-free and literal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
