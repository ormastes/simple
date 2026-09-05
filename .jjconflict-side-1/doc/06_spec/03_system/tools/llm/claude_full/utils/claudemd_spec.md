# Claude Full ClaudeMD Slice

> Focused Simple coverage for memory file query helpers from utils/claudemd.ts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full ClaudeMD Slice

Focused Simple coverage for memory file query helpers from utils/claudemd.ts.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/claudemd_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Focused Simple coverage for memory file query helpers from utils/claudemd.ts.

## Scenarios

### Claude full claudemd parity

#### should model memory file path detection

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should model memory file path detection
- Check memory paths
   - Expected: isMemoryFilePathRoute("CLAUDE.md") is true
   - Expected: isMemoryFilePathRoute("x/CLAUDE.local.md") is true
   - Expected: isMemoryFilePathRoute("x/.claude/rules/a.md") is true
   - Expected: isMemoryFilePathRoute("x/.claude/rules/a.txt") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model memory file path detection")
step("Check memory paths")
expect(isMemoryFilePathRoute("CLAUDE.md")).to_equal(true)
expect(isMemoryFilePathRoute("x/CLAUDE.local.md")).to_equal(true)
expect(isMemoryFilePathRoute("x/.claude/rules/a.md")).to_equal(true)
expect(isMemoryFilePathRoute("x/.claude/rules/a.txt")).to_equal(false)
```

</details>

#### should model large memory files

- should model large memory files
- Check large files
   - Expected: getLargeMemoryFilesRoute(40000) is false
   - Expected: getLargeMemoryFilesRoute(40001) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model large memory files")
step("Check large files")
expect(getLargeMemoryFilesRoute(40000)).to_equal(false)
expect(getLargeMemoryFilesRoute(40001)).to_equal(true)
```

</details>

#### should model external includes

- should model external includes
- Check external include helpers
   - Expected: getExternalClaudeMdIncludesRoute("User", true, false) is false
   - Expected: getExternalClaudeMdIncludesRoute("Project", true, false) is true
   - Expected: getExternalClaudeMdIncludesRoute("Project", false, false) is false
   - Expected: getExternalClaudeMdIncludesRoute("Project", true, true) is false
   - Expected: hasExternalClaudeMdIncludesRoute(0) is false
   - Expected: hasExternalClaudeMdIncludesRoute(1) is true
   - Expected: memoryFileInfoRoute("/repo/CLAUDE.md", "Project") equals `Project:/repo/CLAUDE.md`
   - Expected: externalClaudeMdIncludeRoute("/other/CLAUDE.md", "/repo/CLAUDE.md") equals `/repo/CLAUDE.md -> /other/CLAUDE.md`
   - Expected: claudemdSourceLinesModeled() equals `1479`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model external includes")
step("Check external include helpers")
expect(getExternalClaudeMdIncludesRoute("User", true, false)).to_equal(false)
expect(getExternalClaudeMdIncludesRoute("Project", true, false)).to_equal(true)
expect(getExternalClaudeMdIncludesRoute("Project", false, false)).to_equal(false)
expect(getExternalClaudeMdIncludesRoute("Project", true, true)).to_equal(false)
expect(hasExternalClaudeMdIncludesRoute(0)).to_equal(false)
expect(hasExternalClaudeMdIncludesRoute(1)).to_equal(true)
expect(memoryFileInfoRoute("/repo/CLAUDE.md", "Project")).to_equal("Project:/repo/CLAUDE.md")
expect(externalClaudeMdIncludeRoute("/other/CLAUDE.md", "/repo/CLAUDE.md")).to_equal("/repo/CLAUDE.md -> /other/CLAUDE.md")
expect(claudemdSourceLinesModeled()).to_equal(1479)
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

- Canonical SPipe generation for source `176d3ecfa7a96eadd31c2c88ae44893559927f0105b06611d7df8f74483d5208`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `176d3ecfa7a96eadd31c2c88ae44893559927f0105b06611d7df8f74483d5208`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `176d3ecfa7a96eadd31c2c88ae44893559927f0105b06611d7df8f74483d5208`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/utils/claudemd_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/claudemd_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/claudemd_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/claudemd_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/claudemd_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/claudemd_spec.spl:18:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model memory file path detection' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/claudemd_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model memory file path detection' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/claudemd_spec.spl:27:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model large memory files' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/claudemd_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model large memory files' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/claudemd_spec.spl:34:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model external includes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/claudemd_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model external includes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
