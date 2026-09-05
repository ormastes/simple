# Claude Full Diff, Doctor, and Exit Commands

> Checks modern SSpec parity for the small command descriptors.

<!-- sdn-diagram:id=diff_doctor_exit_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=diff_doctor_exit_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

diff_doctor_exit_spec -> std
diff_doctor_exit_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=diff_doctor_exit_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Diff, Doctor, and Exit Commands

Checks modern SSpec parity for the small command descriptors.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/diff_doctor_exit_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for the small command descriptors.

## Scenarios

### Claude full diff doctor exit commands

#### should expose diff and doctor commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(diffCommandTarget()).to_equal("diff")
expect(diffCommandName()).to_equal("diff")
expect(doctorCommandTarget()).to_equal("doctor")
expect(doctorCommandDescription()).to_contain("health")
```

</details>

#### should model exit behavior

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(exitCommandName()).to_equal("exit")
expect(exitCommand().aliases.len()).to_equal(2)
expect(runExitCommand().shouldExit).to_equal(true)
expect(runExitCommand().display).to_equal("system")
```

</details>

#### should expose source sizes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(diffCommandSourceLinesModeled()).to_equal(8)
expect(diffIndexSourceLinesModeled()).to_equal(8)
expect(doctorCommandSourceLinesModeled()).to_equal(6)
expect(doctorIndexSourceLinesModeled()).to_equal(12)
expect(exitCommandSourceLinesModeled()).to_equal(32)
expect(exitIndexSourceLinesModeled()).to_equal(12)
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
