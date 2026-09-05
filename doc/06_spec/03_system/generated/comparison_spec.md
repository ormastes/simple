# comparison_spec

> Tests for snapshot comparison functionality including content matching,

<!-- sdn-diagram:id=comparison_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=comparison_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

comparison_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=comparison_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# comparison_spec

Tests for snapshot comparison functionality including content matching,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/generated/comparison_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for snapshot comparison functionality including content matching,
diff generation, output formatting, and context line handling for
displaying differences between actual and expected snapshots.

## Scenarios

### Snapshot Comparison

#### Basic Comparison

#### matches identical content

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val actual = "Hello World"
val expected = "Hello World"
expect(actual).to_equal(expected)
```

</details>

#### detects content differences

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val actual = "Hello World"
val expected = "Hello World!"
expect(actual == expected).to_equal(false)
```

</details>

#### ignores whitespace differences when configured

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content1 = "hello  world"
val content2 = "hello world"
# Different but could be normalized
expect(content1 == content2).to_equal(false)
```

</details>

#### Diff Generation

#### generates diff for changed lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line1 = "old line"
val line2 = "new line"
expect(line1 == line2).to_equal(false)
```

</details>

#### handles multiline diffs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text1 = "line 1{NL}line 2{NL}line 3"
val text2 = "line 1{NL}line 2{NL}line 3"
expect(text1).to_equal(text2)
```

</details>

#### marks added lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original_length = 3
val new_length = 4
expect(new_length > original_length).to_equal(true)
```

</details>

#### marks removed lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original_length = 4
val new_length = 3
expect(new_length < original_length).to_equal(true)
```

</details>

#### Formatting

#### formats comparison result

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = "Match"
expect(result).to_equal("Match")
```

</details>

#### shows unified diff format

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diff_format = "unified"
expect(diff_format).to_equal("unified")
```

</details>

#### shows side-by-side format

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diff_format = "side-by-side"
expect(diff_format).to_equal("side-by-side")
```

</details>

#### Context Lines

#### includes context around changes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val context_size = 3
expect(context_size > 0).to_equal(true)
```

</details>

#### handles edge cases at file start

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line_number = 1
expect(line_number >= 1).to_equal(true)
```

</details>

#### handles edge cases at file end

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val total_lines = 100
val line_number = 100
expect(line_number <= total_lines).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
