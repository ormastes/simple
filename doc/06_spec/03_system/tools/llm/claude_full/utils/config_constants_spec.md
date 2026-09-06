# Claude Full config constants

> Pure Simple coverage for dependency-free config constants.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full config constants

Pure Simple coverage for dependency-free config constants.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/config_constants_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for dependency-free config constants.

## Scenarios

### Claude full config constants

#### exposes notification channels in TS order

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- exposes notification channels in TS order
- Check notification channel list
   - Expected: notificationChannels() equals `["auto", "iterm2", "iterm2_with_bell", "terminal_bell", "kitty", "ghostty", "... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exposes notification channels in TS order")
step("Check notification channel list")
expect(notificationChannels()).to_equal(["auto", "iterm2", "iterm2_with_bell", "terminal_bell", "kitty", "ghostty", "notifications_disabled"])
```

</details>

#### exposes supported editor modes without deprecated emacs

- exposes supported editor modes without deprecated emacs
- Check editor modes
   - Expected: editorModes() equals `["normal", "vim"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exposes supported editor modes without deprecated emacs")
step("Check editor modes")
expect(editorModes()).to_equal(["normal", "vim"])
```

</details>

#### exposes teammate spawn modes in TS order

- exposes teammate spawn modes in TS order
- Check teammate modes
   - Expected: teammateModes() equals `["auto", "tmux", "in-process"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exposes teammate spawn modes in TS order")
step("Check teammate modes")
expect(teammateModes()).to_equal(["auto", "tmux", "in-process"])
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

- Canonical SPipe generation for source `1764cbef6cd0ae2594851b7bdcbfa1fd68629c0962794d85a82eed2b38fe6067`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1764cbef6cd0ae2594851b7bdcbfa1fd68629c0962794d85a82eed2b38fe6067`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1764cbef6cd0ae2594851b7bdcbfa1fd68629c0962794d85a82eed2b38fe6067`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/llm/claude_full/utils/config_constants_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/config_constants_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/config_constants_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/config_constants_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/config_constants_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes notification channels in TS order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/config_constants_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes supported editor modes without deprecated emacs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/config_constants_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes teammate spawn modes in TS order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
