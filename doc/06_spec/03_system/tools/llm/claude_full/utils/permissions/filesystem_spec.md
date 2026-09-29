# Claude Full Filesystem Permissions Slice

> Focused Simple coverage for pure filesystem permission helpers from

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Filesystem Permissions Slice

Focused Simple coverage for pure filesystem permission helpers from

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/permissions/filesystem_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Focused Simple coverage for pure filesystem permission helpers from
utils/permissions/filesystem.ts.

## Scenarios

### Claude full filesystem permissions parity

#### should model path normalization helpers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should model path normalization helpers
- Check normalization
   - Expected: normalizeCaseForComparison("A/B") equals `a/b`
   - Expected: normalizeCaseForComparison(".cLauDe/Settings.json") equals `.claude/settings.json`
   - Expected: relativePathRoute("/repo", "/repo/a/b", false) equals `a/b`
   - Expected: relativePathRoute("C:\\repo", "C:\\repo\\a\\b", true) equals `a/b`
   - Expected: toPosixPathRoute("a/b", false) equals `a/b`
   - Expected: toPosixPathRoute("a\\b", true) equals `a/b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model path normalization helpers")
step("Check normalization")
expect(normalizeCaseForComparison("A/B")).to_equal("a/b")
expect(normalizeCaseForComparison(".cLauDe/Settings.json")).to_equal(".claude/settings.json")
expect(relativePathRoute("/repo", "/repo/a/b", false)).to_equal("a/b")
expect(relativePathRoute("C:\\repo", "C:\\repo\\a\\b", true)).to_equal("a/b")
expect(toPosixPathRoute("a/b", false)).to_equal("a/b")
expect(toPosixPathRoute("a\\b", true)).to_equal("a/b")
```

</details>

#### should model claude skill scope hardening

- should model claude skill scope hardening
- Check skill scope
   - Expected: getClaudeSkillScopeRoute("/repo/file.txt", "/home/u/.claude", "/repo", false) equals `none`
   - Expected: getClaudeSkillScopeRoute("/repo/.claude/skills/", "/home/u/.claude", "/repo", false) equals `none`
   - Expected: getClaudeSkillScopeRoute("/repo/.claude/skills/../x", "/home/u/.claude", "/repo", false) equals `none`
   - Expected: getClaudeSkillScopeRoute("/repo/.claude/skills/bad*/x", "/home/u/.claude", "/repo", false) equals `none`
   - Expected: getClaudeSkillScopeRoute("/repo/.claude/skills/MySkill/x", "/home/u/.claude", "/repo", false) equals `project skill MySkill`
   - Expected: getClaudeSkillScopeRoute("/home/u/.claude/skills/MySkill/x", "/home/u/.claude", "/repo", false) equals `global skill MySkill`
   - Expected: dangerousFileRoute(".env") is true
   - Expected: dangerousDirectoryRoute(".ssh") is true
   - Expected: filesystemPermissionsSourceLinesModeled() equals `1777`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model claude skill scope hardening")
step("Check skill scope")
expect(getClaudeSkillScopeRoute("/repo/file.txt", "/home/u/.claude", "/repo", false)).to_equal("none")
expect(getClaudeSkillScopeRoute("/repo/.claude/skills/", "/home/u/.claude", "/repo", false)).to_equal("none")
expect(getClaudeSkillScopeRoute("/repo/.claude/skills/../x", "/home/u/.claude", "/repo", false)).to_equal("none")
expect(getClaudeSkillScopeRoute("/repo/.claude/skills/bad*/x", "/home/u/.claude", "/repo", false)).to_equal("none")
expect(getClaudeSkillScopeRoute("/repo/.claude/skills/MySkill/x", "/home/u/.claude", "/repo", false)).to_equal("project skill MySkill")
expect(getClaudeSkillScopeRoute("/home/u/.claude/skills/MySkill/x", "/home/u/.claude", "/repo", false)).to_equal("global skill MySkill")
expect(dangerousFileRoute(".env")).to_equal(true)
expect(dangerousDirectoryRoute(".ssh")).to_equal(true)
expect(filesystemPermissionsSourceLinesModeled()).to_equal(1777)
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

- Canonical SPipe generation for source `0edf8914c5a71716af0321ca1e26c7157d83e75ebfc2dc66bdac6edb30fc6d82`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0edf8914c5a71716af0321ca1e26c7157d83e75ebfc2dc66bdac6edb30fc6d82`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0edf8914c5a71716af0321ca1e26c7157d83e75ebfc2dc66bdac6edb30fc6d82`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/tools/llm/claude_full/utils/permissions/filesystem_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/permissions/filesystem_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=90
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/permissions/filesystem_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/permissions/filesystem_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/permissions/filesystem_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/permissions/filesystem_spec.spl:19:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model path normalization helpers' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/permissions/filesystem_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model path normalization helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/permissions/filesystem_spec.spl:30:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model claude skill scope hardening' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/permissions/filesystem_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model claude skill scope hardening' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
