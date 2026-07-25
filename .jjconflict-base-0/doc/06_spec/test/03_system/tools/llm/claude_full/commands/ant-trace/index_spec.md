# Claude Full Ant Trace Command

> Mirrors `tmp/claude/claude-code-main/src/commands/ant-trace/index.js` for the

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

# Claude Full Ant Trace Command

Mirrors `tmp/claude/claude-code-main/src/commands/ant-trace/index.js` for the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/ant-trace/index_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors `tmp/claude/claude-code-main/src/commands/ant-trace/index.js` for the
stub command object slice: hidden, disabled, and named `stub`.

## Scenarios

### Claude full ant-trace command

#### matches Claude's hidden disabled stub default command

- Load the default command object
- Verify the stub command metadata and disabled gate
   - Expected: command.name equals `stub`
   - Expected: command.isHidden is true
   - Expected: command.isEnabled() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Load the default command object")
val command = defaultCommand()

step("Verify the stub command metadata and disabled gate")
expect(command.name).to_equal("stub")
expect(command.isHidden).to_equal(true)
expect(command.isEnabled()).to_equal(false)
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
