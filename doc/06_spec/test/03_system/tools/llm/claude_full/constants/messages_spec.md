# Claude Full Constants

> Mirrors the smallest Claude constant-only source files so the full-parity

<!-- sdn-diagram:id=messages_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=messages_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

messages_spec -> std
messages_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=messages_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Constants

Mirrors the smallest Claude constant-only source files so the full-parity

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/constants/messages_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors the smallest Claude constant-only source files so the full-parity
matrix has executable evidence for literal values, not just target paths.

## Scenarios

### Claude full constant parity

#### should expose the no-content placeholder used by Claude output

- Read the constant mapped from constants/messages.ts
   - Expected: NO_CONTENT_MESSAGE equals `(no content)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the constant mapped from constants/messages.ts")
expect(NO_CONTENT_MESSAGE).to_equal("(no content)")
```

</details>

#### should expose the Config tool name literal

- Read the constant mapped from tools/ConfigTool/constants.ts
   - Expected: CONFIG_TOOL_NAME equals `Config`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the constant mapped from tools/ConfigTool/constants.ts")
expect(CONFIG_TOOL_NAME).to_equal("Config")
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
