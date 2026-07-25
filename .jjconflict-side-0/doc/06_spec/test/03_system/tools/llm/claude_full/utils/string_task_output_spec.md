# Claude Full String and Task Output Utilities

> Checks modern SSpec parity for string accumulation and disk task output.

<!-- sdn-diagram:id=string_task_output_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=string_task_output_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

string_task_output_spec -> std
string_task_output_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=string_task_output_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full String and Task Output Utilities

Checks modern SSpec parity for string accumulation and disk task output.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/string_task_output_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for string accumulation and disk task output.

## Scenarios

### Claude full string and task output utilities

#### should model safe string helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(capitalize("fooBar")).to_equal("FooBar")
expect(plural(1, "file", "")).to_equal("file")
expect(plural(3, "file", "")).to_equal("files")
expect(firstLineOf("a\nb")).to_equal("a")
expect(countCharInString("a,b,c", ",", 0)).to_equal(2)
expect(normalizeFullWidthDigits("１２3")).to_equal("123")
expect(normalizeFullWidthSpace("a　b")).to_equal("a b")
```

</details>

#### should truncate safe joins and accumulated output

- var acc = EndTruncatingAccumulator new
- acc = acc append
   - Expected: acc.length() equals `5`
   - Expected: acc.truncated() is true
   - Expected: acc.totalBytes() equals `8`
   - Expected: acc.clear().length() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(safeJoinLines(["abc", "def"], ",", 5)).to_contain("truncated")
var acc = EndTruncatingAccumulator.new(5)
acc = acc.append("abc").append("defgh")
expect(acc.length()).to_equal(5)
expect(acc.truncated()).to_equal(true)
expect(acc.totalBytes()).to_equal(8)
expect(acc.toString()).to_contain("output truncated")
expect(acc.clear().length()).to_equal(0)
```

</details>

#### should model disk task output queue cap flush and tail read

- var output = DiskTaskOutput new
   - Expected: output.path equals `/tmp/project/session-1/tasks/task-1.output`
- output = output append
   - Expected: output.queue.len() equals `0`
   - Expected: output.getStdout(5) equals `world`
- output = output cancel
   - Expected: output.canceled is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dir = getTaskOutputDir("/tmp/project", "session-1")
var output = DiskTaskOutput.new("task-1", dir)
expect(output.path).to_equal("/tmp/project/session-1/tasks/task-1.output")
output = output.append("hello").append(" world").flush()
expect(output.queue.len()).to_equal(0)
expect(output.getStdout(5)).to_equal("world")
output = output.cancel()
expect(output.canceled).to_equal(true)
expect(makeTaskOutputTruncationMessage()).to_contain("5GB")
```

</details>

#### should expose source sizes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(stringUtilsSourceLinesModeled()).to_equal(235)
expect(diskOutputSourceLinesModeled()).to_equal(451)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
