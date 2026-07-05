# Claude Full Stub Commands

> Mirrors one-line Claude command index files that export hidden disabled stub

<!-- sdn-diagram:id=stub_commands_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=stub_commands_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

stub_commands_spec -> std
stub_commands_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=stub_commands_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Stub Commands

Mirrors one-line Claude command index files that export hidden disabled stub

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/stub_commands_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors one-line Claude command index files that export hidden disabled stub
commands.

## Scenarios

### Claude full stub command indexes

#### should expose hidden disabled bughunter, issue, and onboarding commands

- Load the first stub command batch
- Check Claude's shared stub-command metadata
- assert stub command
- assert stub command
- assert stub command


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Load the first stub command batch")
val bughunter = bughunterCommand()
val issue = issueCommand()
val onboarding = onboardingCommand()

step("Check Claude's shared stub-command metadata")
assert_stub_command(bughunter.name, bughunter.isHidden, bughunter.isEnabled())
assert_stub_command(issue.name, issue.isHidden, issue.isEnabled())
assert_stub_command(onboarding.name, onboarding.isHidden, onboarding.isEnabled())
```

</details>

#### should expose hidden disabled share, summary, and teleport commands

- Load the second stub command batch
- Check Claude's shared stub-command metadata
- assert stub command
- assert stub command
- assert stub command


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Load the second stub command batch")
val share = shareCommand()
val summary = summaryCommand()
val teleport = teleportCommand()

step("Check Claude's shared stub-command metadata")
assert_stub_command(share.name, share.isHidden, share.isEnabled())
assert_stub_command(summary.name, summary.isHidden, summary.isEnabled())
assert_stub_command(teleport.name, teleport.isHidden, teleport.isEnabled())
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
