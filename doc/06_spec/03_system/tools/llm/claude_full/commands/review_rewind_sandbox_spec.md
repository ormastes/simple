# Claude Full Review, Rewind, and Sandbox Commands

> Checks modern SSpec parity for review helpers, rewind, and sandbox toggle.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Review, Rewind, and Sandbox Commands

Checks modern SSpec parity for review helpers, rewind, and sandbox toggle.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/review_rewind_sandbox_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for review helpers, rewind, and sandbox toggle.

`REQ-LLM-CARET-HIDDEN-008` applies only to the review/ultrareview gate
scenario. Rewind, sandbox-toggle, and source-parity assertions are supporting
command evidence, not hidden-feature fulfillment.

The trace-authoritative sandbox owners use hyphenated filesystem paths. Their
canonical index delegates to the compiler-addressable underscore module used
for behavioral calls below; source-parity checks read the hyphenated owners
directly so the underscore shadow is not presented as the traced source.

This source-synchronized specification does not claim execution in the current
runtime-blocked tranche.

## Scenarios

### Claude full review rewind sandbox commands

### REQ-LLM-CARET-HIDDEN-008: review and ultrareview gates

#### should expose review entitlement and overage boundaries

- should expose review entitlement and overage boundaries
- Check review ultrareview entitlement and overage boundary behavior
   - Expected: reviewCommandName() equals `review`
   - Expected: reviewPrompt("diff") equals `Review these changes: diff`
   - Expected: ultrareviewCommandName() equals `ultrareview`
   - Expected: ultrareviewPrompt("workspace") equals `Run ultra review for workspace`
   - Expected: ultrareviewOverageMessage(above) equals `Ultra review usage 11/10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-LLM-CARET-HIDDEN-008 REQ-SSPEC-SYSTEM
step("should expose review entitlement and overage boundaries")
step("Check review ultrareview entitlement and overage boundary behavior")
expect(reviewCommandName()).to_equal("review")
expect(reviewPrompt("diff")).to_equal("Review these changes: diff")
expect(ultrareviewCommandName()).to_equal("ultrareview")
expect(ultrareviewPrompt("workspace")).to_equal("Run ultra review for workspace")
expect(ultrareviewEnabled(true, true)).to_be(true)
expect(ultrareviewEnabled(true, false)).to_be(false)
expect(ultrareviewEnabled(false, true)).to_be(false)
val below = UltrareviewOverage.new(9, 10)
val equal = UltrareviewOverage.new(10, 10)
val above = UltrareviewOverage.new(11, 10)
expect(ultrareviewIsOverLimit(below)).to_be(false)
expect(ultrareviewIsOverLimit(equal)).to_be(false)
expect(ultrareviewIsOverLimit(above)).to_be(true)
expect(ultrareviewOverageMessage(above)).to_equal("Ultra review usage 11/10")
```

</details>

### supporting rewind sandbox and source parity

#### should model rewind and sandbox toggle behavior

- should model rewind and sandbox toggle behavior
- Check rewind and sandbox toggle behavior
   - Expected: rewindIndexName() equals `rewind`
   - Expected: sandboxToggleCommandName() equals `sandbox-toggle`
   - Expected: sandboxToggleMessage(enabled) equals `Sandbox enabled`
   - Expected: sandboxToggleMessage(disabled) equals `Sandbox disabled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model rewind and sandbox toggle behavior")
step("Check rewind and sandbox toggle behavior")
expect(rewindIndexName()).to_equal("rewind")
expect(sandboxToggleCommandName()).to_equal("sandbox-toggle")
val state = SandboxToggleState.new(false)
val enabled = toggleSandbox(state)
expect(enabled.enabled).to_be(true)
expect(sandboxToggleMessage(enabled)).to_equal("Sandbox enabled")
val disabled = toggleSandbox(enabled)
expect(disabled.enabled).to_be(false)
expect(sandboxToggleMessage(disabled)).to_equal("Sandbox disabled")
```

</details>

#### should expose review rewind and sandbox source parity

- should expose review rewind and sandbox source parity
- Check review rewind and sandbox source parity
   - Expected: reviewSourceLinesModeled() equals `57`
   - Expected: ultrareviewCommandSourceLinesModeled() equals `57`
   - Expected: ultrareviewEnabledSourceLinesModeled() equals `14`
   - Expected: ultrareviewOverageDialogSourceLinesModeled() equals `95`
   - Expected: rewindSourceLinesModeled() equals `13`
   - Expected: rewindIndexSourceLinesModeled() equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose review rewind and sandbox source parity")
step("Check review rewind and sandbox source parity")
expect(reviewSourceLinesModeled()).to_equal(57)
expect(ultrareviewCommandSourceLinesModeled()).to_equal(57)
expect(ultrareviewEnabledSourceLinesModeled()).to_equal(14)
expect(ultrareviewOverageDialogSourceLinesModeled()).to_equal(95)
expect(rewindSourceLinesModeled()).to_equal(13)
expect(rewindIndexSourceLinesModeled()).to_equal(13)
val canonicalSandbox = file_read("doc/11_archive/llm_caret_claude_full_hyphen_port/commands/sandbox-toggle/sandbox-toggle.spl") ?? ""
val canonicalSandboxIndex = file_read("src/app/llm_caret/claude_full/commands/sandbox-toggle/index.spl") ?? ""
expect(countSourceLines(canonicalSandbox)).to_be_greater_than(81)
expect(countSourceLines(canonicalSandboxIndex)).to_be_greater_than(49)
expect(canonicalSandbox).to_contain("fn sandboxToggleCommandName() -> text:\n    \"sandbox-toggle\"")
expect(canonicalSandbox).to_contain("fn toggleSandbox(state: SandboxToggleState) -> SandboxToggleState:\n    SandboxToggleState.new(not state.enabled)")
expect(canonicalSandbox).to_contain("fn sandboxToggleMessage(state: SandboxToggleState) -> text:\n    if state.enabled:\n        return \"Sandbox enabled\"\n    \"Sandbox disabled\"")
expect(canonicalSandboxIndex).to_contain("use app.llm_caret.claude_full.commands.sandbox_toggle.sandbox_toggle.*")
expect(canonicalSandboxIndex).to_contain("fn sandboxToggleIndexName() -> text:\n    \"sandbox-toggle\"")
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
- `REQ-LLM-CARET-HIDDEN-008`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0556474ae9f058c0929a1e9a87657fac3d34a160cfd6eaf34856e4295be04837`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0556474ae9f058c0929a1e9a87657fac3d34a160cfd6eaf34856e4295be04837`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0556474ae9f058c0929a1e9a87657fac3d34a160cfd6eaf34856e4295be04837`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **82/100**; blockers: **0**.

SSpec documentization score: 82/100
source: test/03_system/tools/llm/claude_full/commands/review_rewind_sandbox_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/commands/review_rewind_sandbox_spec.md (current)
findings: 10 blockers: 0
  narrative=100 structure=85 oracle=70
  traceability=100 evidence=70 coverage=80 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/commands/review_rewind_sandbox_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/commands/review_rewind_sandbox_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/commands/review_rewind_sandbox_spec.spl:1:1: advice SSDOC-COV-001 [coverage] (-20): the authored requirement defines adverse behavior but no adverse scenario is named
  why: Specifications should explain behavior outside the happy path.
  improve: Add adverse-path scenarios required by the source, or record a reasoned suppression.
test/03_system/tools/llm/claude_full/commands/review_rewind_sandbox_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/commands/review_rewind_sandbox_spec.spl:48:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose review entitlement and overage boundaries' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/commands/review_rewind_sandbox_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose review entitlement and overage boundaries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/commands/review_rewind_sandbox_spec.spl:68:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model rewind and sandbox toggle behavior' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/commands/review_rewind_sandbox_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model rewind and sandbox toggle behavior' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/commands/review_rewind_sandbox_spec.spl:82:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose review rewind and sandbox source parity' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/commands/review_rewind_sandbox_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose review rewind and sandbox source parity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
