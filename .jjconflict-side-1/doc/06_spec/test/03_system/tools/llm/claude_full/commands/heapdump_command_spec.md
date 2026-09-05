# Claude Full Heapdump Command

> Checks modern SSpec parity for heapdump command descriptors.

<!-- sdn-diagram:id=heapdump_command_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=heapdump_command_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

heapdump_command_spec -> std
heapdump_command_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=heapdump_command_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Heapdump Command

Checks modern SSpec parity for heapdump command descriptors.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/heapdump_command_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for heapdump command descriptors.

## Scenarios

### Claude full heapdump command

#### should expose heapdump command metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(heapdumpCommandName()).to_equal("heapdump")
expect(heapdumpCommand().description).to_contain("heap")
expect(heapdumpCommand().typeName).to_equal("local")
```

</details>

#### should expose source sizes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(heapdumpCommandSourceLinesModeled()).to_equal(17)
expect(heapdumpIndexSourceLinesModeled()).to_equal(12)
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
