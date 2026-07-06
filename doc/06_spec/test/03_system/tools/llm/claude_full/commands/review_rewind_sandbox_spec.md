# Claude Full Review, Rewind, and Sandbox Commands

> Checks modern SSpec parity for review helpers, rewind, and sandbox toggle.

<!-- sdn-diagram:id=review_rewind_sandbox_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=review_rewind_sandbox_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

review_rewind_sandbox_spec -> std
review_rewind_sandbox_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=review_rewind_sandbox_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for review helpers, rewind, and sandbox toggle.

## Scenarios

### Claude full review rewind sandbox commands

#### should expose review and ultrareview behavior

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(reviewCommandName()).to_equal("review")
expect(reviewPrompt("diff")).to_contain("diff")
expect(ultrareviewCommandName()).to_equal("ultrareview")
expect(ultrareviewEnabled(true, true)).to_equal(true)
expect(ultrareviewIsOverLimit(UltrareviewOverage.new(11, 10))).to_equal(true)
```

</details>

#### should model rewind and sandbox toggle

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rewindIndexName()).to_equal("rewind")
val state = SandboxToggleState.new(false)
expect(toggleSandbox(state).enabled).to_equal(true)
expect(sandboxToggleMessage(toggleSandbox(state))).to_contain("enabled")
expect(sandboxToggleIndexName()).to_equal("sandbox-toggle")
```

</details>

#### should expose source sizes

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(reviewSourceLinesModeled()).to_equal(57)
expect(ultrareviewCommandSourceLinesModeled()).to_equal(57)
expect(ultrareviewEnabledSourceLinesModeled()).to_equal(14)
expect(ultrareviewOverageDialogSourceLinesModeled()).to_equal(95)
expect(rewindSourceLinesModeled()).to_equal(13)
expect(rewindIndexSourceLinesModeled()).to_equal(13)
expect(sandboxToggleSourceLinesModeled()).to_equal(82)
expect(sandboxToggleIndexSourceLinesModeled()).to_equal(50)
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
