# Claude Full Review, Rewind, and Sandbox Commands

> Source-synchronized command evidence for review, ultrareview, rewind, and
> sandbox-toggle helpers.

| Tests | Active | Skipped | Pending |
|---|---:|---:|---:|
| 3 | 3 | 0 | 0 |

## Status and scope

- Executable source: `test/03_system/tools/llm/claude_full/commands/review_rewind_sandbox_spec.spl`
- Execution in this tranche: **0 scenarios executed; no PASS is claimed**
- Runtime/docgen status: blocked until a qualified self-hosted Simple runtime is available
- Requirement: `REQ-LLM-CARET-HIDDEN-008` applies only to the first
  review/ultrareview scenario
- Exclusion: rewind, sandbox-toggle, and source-parity assertions are
  supporting command evidence, not hidden-feature fulfillment
- Reachability: Claude-full parts-bin only; no shipped Caret CLI/TUI admission
  is claimed

## Helper and owner contract

`countSourceLines(text_value)` is a test-local source-parity helper. It starts
at zero and adds one for each newline byte; it does not select the source owner.

The trace-authoritative sandbox owners are
`commands/sandbox-toggle/sandbox-toggle.spl` and
`commands/sandbox-toggle/index.spl`. The canonical index explicitly delegates
to `commands.sandbox_toggle.sandbox_toggle`, the compiler-addressable
underscore behavior owner imported by this spec. Behavioral calls therefore
exercise that declared command delegate. Source-parity assertions read both
hyphenated canonical files directly; the underscore index and its modeled-line
metadata are not used. The underscore command is not claimed as the traced
source.

## REQ-LLM-CARET-HIDDEN-008: review and ultrareview gates

### Scenario: should expose review entitlement and overage boundaries

- Check review ultrareview entitlement and overage boundary behavior.
- Expected: review and ultrareview names and prompts remain exact.
- Expected: ultrareview needs both its flag and entitlement.
- Expected: below-limit and equal-limit usage remain allowed, above-limit
  usage is rejected, and the overage message reports exact usage.

<details>
<summary>Executable SSpec</summary>

```simple
it "should expose review entitlement and overage boundaries":
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

## Supporting rewind, sandbox, and source parity

### Scenario: should model rewind and sandbox toggle behavior

- Check rewind and sandbox toggle behavior.
- Expected: rewind and sandbox retain their exact command names.
- Expected: sandbox toggles disabled to enabled and then enabled to disabled,
  with the exact matching status message at each transition.

<details>
<summary>Executable SSpec</summary>

```simple
it "should model rewind and sandbox toggle behavior":
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

### Scenario: should expose review rewind and sandbox source parity

- Check review rewind and sandbox source parity.
- Expected: review, rewind, and sandbox metadata retain accepted modeled-source
  counts.
- Expected: the traced hyphenated sandbox files meet their direct source floor,
  expose the canonical behavior symbols, and record the underscore delegation.

<details>
<summary>Executable SSpec</summary>

```simple
it "should expose review rewind and sandbox source parity":
    step("Check review rewind and sandbox source parity")
    expect(reviewSourceLinesModeled()).to_equal(57)
    expect(ultrareviewCommandSourceLinesModeled()).to_equal(57)
    expect(ultrareviewEnabledSourceLinesModeled()).to_equal(14)
    expect(ultrareviewOverageDialogSourceLinesModeled()).to_equal(95)
    expect(rewindSourceLinesModeled()).to_equal(13)
    expect(rewindIndexSourceLinesModeled()).to_equal(13)
    val canonicalSandbox = file_read("src/app/llm_caret/claude_full/commands/sandbox-toggle/sandbox-toggle.spl") ?? ""
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
