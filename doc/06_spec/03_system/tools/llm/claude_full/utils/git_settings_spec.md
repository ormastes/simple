# Claude Full git settings

> Pure Simple coverage for git instruction inclusion settings.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full git settings

Pure Simple coverage for git instruction inclusion settings.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/git_settings_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for git instruction inclusion settings.

## Scenarios

### Claude full git settings

#### disables git instructions when disable env is truthy

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- disables git instructions when disable env is truthy
- Check truthy disable env
   - Expected: shouldIncludeGitInstructions(Some("1"), Some(true)) is false
   - Expected: shouldIncludeGitInstructions(Some("yes"), nil) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("disables git instructions when disable env is truthy")
step("Check truthy disable env")
expect(shouldIncludeGitInstructions(Some("1"), Some(true))).to_equal(false)
expect(shouldIncludeGitInstructions(Some("yes"), nil)).to_equal(false)
```

</details>

#### includes git instructions when disable env is defined falsy

- includes git instructions when disable env is defined falsy
- Check explicit env enable
   - Expected: shouldIncludeGitInstructions(Some("0"), Some(false)) is true
   - Expected: shouldIncludeGitInstructions(Some("off"), nil) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("includes git instructions when disable env is defined falsy")
step("Check explicit env enable")
expect(shouldIncludeGitInstructions(Some("0"), Some(false))).to_equal(true)
expect(shouldIncludeGitInstructions(Some("off"), nil)).to_equal(true)
```

</details>

#### uses settings when env is absent or unrecognized

- uses settings when env is absent or unrecognized
- Check setting fallback
   - Expected: shouldIncludeGitInstructions(nil, Some(false)) is false
   - Expected: shouldIncludeGitInstructions(Some("maybe"), Some(true)) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses settings when env is absent or unrecognized")
step("Check setting fallback")
expect(shouldIncludeGitInstructions(nil, Some(false))).to_equal(false)
expect(shouldIncludeGitInstructions(Some("maybe"), Some(true))).to_equal(true)
```

</details>

#### defaults to including git instructions

- defaults to including git instructions
- Check default
   - Expected: shouldIncludeGitInstructions(nil, nil) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defaults to including git instructions")
step("Check default")
expect(shouldIncludeGitInstructions(nil, nil)).to_equal(true)
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

- Canonical SPipe generation for source `eeac6b2d11aa5c5688d4d7817fffb9c91fe94410825fcc2c6f4ee10a6f7fe66c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eeac6b2d11aa5c5688d4d7817fffb9c91fe94410825fcc2c6f4ee10a6f7fe66c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eeac6b2d11aa5c5688d4d7817fffb9c91fe94410825fcc2c6f4ee10a6f7fe66c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/llm/claude_full/utils/git_settings_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/git_settings_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/git_settings_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/git_settings_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/git_settings_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'disables git instructions when disable env is truthy' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/git_settings_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes git instructions when disable env is defined falsy' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/git_settings_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses settings when env is absent or unrecognized' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
