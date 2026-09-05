# Claude Full Env Command Index

> Mirrors `tmp/claude/claude-code-main/src/commands/env/index.js` for the tiny

<!-- sdn-diagram:id=index_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=index_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

index_spec -> std
index_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=index_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Env Command Index

Mirrors `tmp/claude/claude-code-main/src/commands/env/index.js` for the tiny

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/env/index_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors `tmp/claude/claude-code-main/src/commands/env/index.js` for the tiny
default command slice: the command is hidden, disabled, and named `stub`.

## Scenarios

### Claude full commands env index

#### exports the hidden disabled stub command

- Read the default command object exported by Claude's env command module
   - Expected: defaultCommand.isHidden is true
   - Expected: defaultCommand.isEnabled() is false
   - Expected: defaultCommand.name equals `stub`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the default command object exported by Claude's env command module")
expect(defaultCommand.isHidden).to_equal(true)
expect(defaultCommand.isEnabled()).to_equal(false)
expect(defaultCommand.name).to_equal("stub")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
