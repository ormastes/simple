# Claude Full Help and Hooks Commands

> Checks modern SSpec parity for help and hooks descriptors.

<!-- sdn-diagram:id=help_hooks_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=help_hooks_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

help_hooks_spec -> std
help_hooks_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=help_hooks_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Help and Hooks Commands

Checks modern SSpec parity for help and hooks descriptors.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/help_hooks_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for help and hooks descriptors.

## Scenarios

### Claude full help hooks commands

#### should expose help and hooks names

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(helpIndexCommandName()).to_equal("help")
expect(hooksIndexCommandName()).to_equal("hooks")
expect(hooksCommandDescription()).to_contain("hook")
```

</details>

#### should expose source sizes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(helpCommandSourceLinesModeled()).to_equal(10)
expect(helpIndexSourceLinesModeled()).to_equal(10)
expect(hooksCommandSourceLinesModeled()).to_equal(12)
expect(hooksIndexSourceLinesModeled()).to_equal(11)
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
