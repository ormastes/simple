# Claude Full PromptInputStashNotice

> Pure Simple/TUI-compatible prompt stash notice.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full PromptInputStashNotice

Pure Simple/TUI-compatible prompt stash notice.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/PromptInput/prompt_input_stash_notice_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple/TUI-compatible prompt stash notice.

## Scenarios

### Claude full PromptInputStashNotice

#### stays hidden when there is no stash

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- stays hidden when there is no stash
- Check guard-return-null shape
   - Expected: view.visible is false
   - Expected: view.text equals ``
   - Expected: promptInputStashNoticeText(false) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stays hidden when there is no stash")
step("Check guard-return-null shape")
val view = PromptInputStashNotice(false)
expect(view.visible).to_equal(false)
expect(view.text).to_equal("")
expect(promptInputStashNoticeText(false)).to_equal("")
```

</details>

#### renders the stash notice when a stash exists

- renders the stash notice when a stash exists
- Check visible TUI metadata
   - Expected: view.visible is true
   - Expected: view.paddingLeft equals `2`
   - Expected: view.dim is true
   - Expected: view.glyph equals `>`
   - Expected: view.sourceGlyph equals `figures.pointerSmall`
   - Expected: view.text equals `Stashed (auto-restores after submit)`
   - Expected: promptInputStashNoticeText(true) equals `> Stashed (auto-restores after submit)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders the stash notice when a stash exists")
step("Check visible TUI metadata")
val view = PromptInputStashNotice(true)
expect(view.visible).to_equal(true)
expect(view.paddingLeft).to_equal(2)
expect(view.dim).to_equal(true)
expect(view.glyph).to_equal(">")
expect(view.sourceGlyph).to_equal("figures.pointerSmall")
expect(view.text).to_equal("Stashed (auto-restores after submit)")
expect(promptInputStashNoticeText(true)).to_equal("> Stashed (auto-restores after submit)")
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

- Canonical SPipe generation for source `c5b28bd54f7b264e08c4d70cbe038f6072582e2fad443a5430d55b60cbff9373`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c5b28bd54f7b264e08c4d70cbe038f6072582e2fad443a5430d55b60cbff9373`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c5b28bd54f7b264e08c4d70cbe038f6072582e2fad443a5430d55b60cbff9373`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/llm/claude_full/components/PromptInput/prompt_input_stash_notice_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/components/PromptInput/prompt_input_stash_notice_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/components/PromptInput/prompt_input_stash_notice_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/components/PromptInput/prompt_input_stash_notice_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/components/PromptInput/prompt_input_stash_notice_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/components/PromptInput/prompt_input_stash_notice_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stays hidden when there is no stash' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/PromptInput/prompt_input_stash_notice_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders the stash notice when a stash exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
