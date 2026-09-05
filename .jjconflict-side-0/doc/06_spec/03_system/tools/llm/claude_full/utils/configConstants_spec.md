# Claude Full config constants

> Pure Simple coverage for dependency-free config constant arrays.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full config constants

Pure Simple coverage for dependency-free config constant arrays.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/configConstants_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for dependency-free config constant arrays.

## Scenarios

### Claude full config constants

#### models notification channel constants

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- models notification channel constants
- Check notification channels
   - Expected: notificationChannels() equals `["auto", "iterm2", "iterm2_with_bell", "terminal_bell", "kitty", "ghostty", "... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("models notification channel constants")
step("Check notification channels")
expect(notificationChannels()).to_equal(["auto", "iterm2", "iterm2_with_bell", "terminal_bell", "kitty", "ghostty", "notifications_disabled"])
```

</details>

#### models editor and teammate mode constants

- models editor and teammate mode constants
- Check mode constants
   - Expected: editorModes() equals `["normal", "vim"]`
   - Expected: teammateModes() equals `["auto", "tmux", "in-process"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("models editor and teammate mode constants")
step("Check mode constants")
expect(editorModes()).to_equal(["normal", "vim"])
expect(teammateModes()).to_equal(["auto", "tmux", "in-process"])
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

- Canonical SPipe generation for source `0a5ab14c5f8486b83c70843106604ec845460b43289faabb51f56b3e822d795e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0a5ab14c5f8486b83c70843106604ec845460b43289faabb51f56b3e822d795e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0a5ab14c5f8486b83c70843106604ec845460b43289faabb51f56b3e822d795e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/tools/llm/claude_full/utils/configConstants_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/configConstants_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/configConstants_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/configConstants_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/configConstants_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'models notification channel constants' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/configConstants_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'models editor and teammate mode constants' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
