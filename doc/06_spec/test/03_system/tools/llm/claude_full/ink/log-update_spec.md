# Claude Full LogUpdate

> Checks the log-update parity slice source contract.

<!-- sdn-diagram:id=log-update_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=log-update_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

log-update_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=log-update_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full LogUpdate

Checks the log-update parity slice source contract.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/ink/log-update_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks the log-update parity slice source contract.

## Scenarios

### Claude full LogUpdate source parity

#### should keep exact source LOC and class line positions

- Read the owned log-update implementation
   - Expected: file_exists(sourcePath()) is true
   - Expected: sourceLineCount() equals `773`
   - Expected: lineAt(43) equals `class LogUpdate:`
   - Expected: lineAt(752) equals `class VirtualScreen:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the owned log-update implementation")
expect(file_exists(sourcePath())).to_equal(true)
expect(sourceLineCount()).to_equal(773)
expect(lineAt(43)).to_equal("class LogUpdate:")
expect(lineAt(752)).to_equal("class VirtualScreen:")
```

</details>

#### should include LogUpdate state, reset, deprecated done cleanup, and render paths

- Check LogUpdate behavior is represented in source


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check LogUpdate behavior is represented in source")
val source = sourceText()
expect(source).to_contain("previousOutput: text")
expect(source).to_contain("me renderPreviousOutput_DEPRECATED(prevFrame: LogFrame) -> [LogDiffOp]:")
expect(source).to_contain("me reset() -> ():")
expect(source).to_contain("me render(prev: LogFrame, next: LogFrame, altScreen: bool, decstbmSafe: bool) -> [LogDiffOp]:")
expect(source).to_contain("return fullResetSequence_CAUSES_FLICKER(next, \"resize\")")
expect(source).to_contain("return fullResetSequence_CAUSES_FLICKER(next, \"offscreen\")")
```

</details>

#### should include virtual cursor transactions and terminal diff operations

- Check VirtualScreen and diff op modeling


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check VirtualScreen and diff op modeling")
val source = sourceText()
expect(source).to_contain("class LogDiffOp:")
expect(source).to_contain("static fn stdout(content: text) -> LogDiffOp:")
expect(source).to_contain("static fn clearTerminal(reason: text) -> LogDiffOp:")
expect(source).to_contain("class VirtualScreen:")
expect(source).to_contain("me txn(patches: [LogDiffOp], dx: i64, dy: i64) -> ():")
expect(source).to_contain("me.cursor.x = me.cursor.x + dx")
expect(source).to_contain("me.cursor.y = me.cursor.y + dy")
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
