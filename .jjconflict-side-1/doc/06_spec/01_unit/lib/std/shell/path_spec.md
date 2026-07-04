# path_spec

> Feature: Path Manipulation

<!-- sdn-diagram:id=path_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=path_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

path_spec -> spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=path_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# path_spec

Feature: Path Manipulation

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/std/shell/path_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Feature: Path Manipulation
Category: Filesystem
Status: Active

## Scenarios

### Path Manipulation

#### basename

#### should extract filename from path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = path_basename("/home/user/file.txt")
expect(result).to_equal("file.txt")
```

</details>

#### should handle path with no directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = path_basename("file.txt")
expect(result).to_equal("file.txt")
```

</details>

#### should handle directory path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = path_basename("/home/user/dir/")
expect(result).to_equal("dir")
```

</details>

#### should handle root path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = path_basename("/")
expect(result).to_equal("")
```

</details>

#### should handle empty path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = path_basename("")
expect(result).to_equal("")
```

</details>

#### dirname

#### should extract directory from path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = path_dirname("/home/user/file.txt")
expect(result).to_equal("/home/user")
```

</details>

#### should handle path with single directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = path_dirname("/file.txt")
expect(result).to_equal("/")
```

</details>

#### should handle relative path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = path_dirname("dir/file.txt")
expect(result).to_equal("dir")
```

</details>

#### should handle file with no directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = path_dirname("file.txt")
expect(result).to_equal("")
```

</details>

#### should handle empty path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = path_dirname("")
expect(result).to_equal("")
```

</details>

#### extension

#### should extract file extension

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = path_ext("/home/user/file.txt")
expect(result).to_equal("txt")
```

</details>

#### should handle multiple dots

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = path_ext("file.tar.gz")
expect(result).to_equal("gz")
```

</details>

#### should handle no extension

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = path_ext("/home/user/file")
expect(result).to_equal("")
```

</details>

#### should handle hidden file with extension

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = path_ext(".bashrc")
expect(result).to_equal("")
```

</details>

#### should handle hidden file with dot and extension

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = path_ext(".config.json")
expect(result).to_equal("json")
```

</details>

#### is_absolute

#### should detect absolute path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = path_is_absolute("/tmp")
expect(result).to_equal(true)
```

</details>

#### should detect relative path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = path_is_absolute("relative/path")
expect(result).to_equal(false)
```

</details>

#### should handle current directory as relative

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = path_is_absolute(".")
expect(result).to_equal(false)
```

</details>

#### should handle parent directory as relative

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = path_is_absolute("..")
expect(result).to_equal(false)
```

</details>

#### join

#### should join path components

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = path_join_many(["home", "user", "file.txt"])
expect(result).to_equal("home/user/file.txt")
```

</details>

#### should handle single component

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = path_join_many(["home"])
expect(result).to_equal("home")
```

</details>

#### should handle empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = path_join_many([])
expect(result).to_equal("")
```

</details>

#### should not add separator if already present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = path_join_two("home/", "user")
expect(result).to_equal("home/user")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
