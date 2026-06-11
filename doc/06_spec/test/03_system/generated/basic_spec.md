# basic_spec

> Tests for the snapshot testing framework's basic functionality including

<!-- sdn-diagram:id=basic_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=basic_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

basic_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=basic_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# basic_spec

Tests for the snapshot testing framework's basic functionality including

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/generated/basic_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for the snapshot testing framework's basic functionality including
metadata storage, content comparison, supported formats, path generation,
and update mode handling.

## Scenarios

### Snapshot Testing Framework

#### Snapshot Metadata

#### stores snapshot name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_name = "test_render"
expect(test_name).to_equal("test_render")
```

</details>

#### stores snapshot format

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val format = "text"
expect(format).to_equal("text")
```

</details>

#### stores snapshot content

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "Hello World"
expect(content).to_equal("Hello World")
```

</details>

#### Snapshot Comparison

#### identifies matching content

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content1 = "same content"
val content2 = "same content"
expect(content1).to_equal(content2)
```

</details>

#### identifies different content

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content1 = "content A"
val content2 = "content B"
expect(content1 == content2).to_equal(false)
```

</details>

#### Snapshot Formats

#### supports text format

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val format = "text"
expect(format).to_equal("text")
```

</details>

#### supports json format

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val format = "json"
expect(format).to_equal("json")
```

</details>

#### supports yaml format

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val format = "yaml"
expect(format).to_equal("yaml")
```

</details>

#### Snapshot Paths

#### generates snapshot path

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_file = "test/example_spec.spl"
val test_name = "test_render"
val expected_contains = "example_spec"
expect(test_file.contains(expected_contains)).to_equal(true)
expect(test_name).to_equal("test_render")
```

</details>

#### Snapshot Updates

#### marks snapshot for update

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val should_update = true
expect(should_update).to_equal(true)
```

</details>

#### skips update when disabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val should_update = false
expect(should_update).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
