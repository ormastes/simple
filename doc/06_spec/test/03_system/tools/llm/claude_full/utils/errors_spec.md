# Claude Full Errors

> Checks error classes and small helper predicates.

<!-- sdn-diagram:id=errors_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=errors_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

errors_spec -> std
errors_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=errors_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Errors

Checks error classes and small helper predicates.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/errors_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks error classes and small helper predicates.

## Scenarios

### Claude full errors

#### should expose core error classes

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ClaudeError.new("bad").name).to_equal("ClaudeError")
expect(MalformedCommandError.new("malformed").message).to_equal("malformed")
expect(AbortError.new("stop").name).to_equal("AbortError")
expect(isAbortErrorName("AbortError")).to_equal(true)
expect(isAbortErrorName("Other")).to_equal(false)
```

</details>

#### should expose config shell and teleport errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = ConfigParseError.new("bad config", "/tmp/c.json", "{}")
expect(config.name).to_equal("ConfigParseError")
expect(config.filePath).to_equal("/tmp/c.json")
val shell = ShellError.new("out", "err", 7, true)
expect(shell.message).to_equal("Shell command failed")
expect(shell.code).to_equal(7)
expect(shell.interrupted).to_equal(true)
val teleport = TeleportOperationError.new("failed", "formatted")
expect(teleport.formattedMessage).to_equal("formatted")
```

</details>

#### should expose telemetry safe error and helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val same = TelemetrySafeError_I_VERIFIED_THIS_IS_NOT_CODE_OR_FILEPATHS.new("timeout", "")
expect(same.name).to_equal("TelemetrySafeError")
expect(same.telemetryMessage).to_equal("timeout")
val redacted = TelemetrySafeError_I_VERIFIED_THIS_IS_NOT_CODE_OR_FILEPATHS.new("timeout /tmp/a", "timeout")
expect(redacted.telemetryMessage).to_equal("timeout")
expect(hasExactErrorMessage("x", "x")).to_equal(true)
expect(isEnoent("ENOENT")).to_equal(true)
expect(isEacces("EACCES")).to_equal(true)
expect(errorsSourceLinesModeled()).to_equal(238)
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
