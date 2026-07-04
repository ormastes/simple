# path_safety_spec

> Boundary specs for the path_is_safe() guard in the HTTP router. Validates rejection of ".." traversal, encoded variants, double-slash, null bytes, and acceptance of normal paths.

<!-- sdn-diagram:id=path_safety_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=path_safety_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

path_safety_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=path_safety_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# path_safety_spec

Boundary specs for the path_is_safe() guard in the HTTP router. Validates rejection of ".." traversal, encoded variants, double-slash, null bytes, and acceptance of normal paths.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SEC-021 |
| Category | HTTP Server Security |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/http_server/path_safety_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Boundary specs for the path_is_safe() guard in the HTTP router.
Validates rejection of ".." traversal, encoded variants, double-slash,
null bytes, and acceptance of normal paths.

## Scenarios

### path_is_safe — dot-dot traversal rejection

#### rejects /../ in middle of path

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(path_is_safe("/../etc/passwd")).to_equal(false)
```

</details>

#### rejects /.. at end of path

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(path_is_safe("/api/..")).to_equal(false)
```

</details>

#### rejects ../ at start

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(path_is_safe("../secret")).to_equal(false)
```

</details>

#### rejects bare ..

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(path_is_safe("..")).to_equal(false)
```

</details>

#### rejects nested traversal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(path_is_safe("/a/b/../../etc/shadow")).to_equal(false)
```

</details>

### path_is_safe — encoded traversal rejection

#### rejects %2e%2e (both dots encoded)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(path_is_safe("/%2e%2e/etc/passwd")).to_equal(false)
```

</details>

#### rejects .%2e (second dot encoded)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(path_is_safe("/.%2e/secret")).to_equal(false)
```

</details>

#### rejects %2e. (first dot encoded)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(path_is_safe("/%2e./secret")).to_equal(false)
```

</details>

#### rejects uppercase %2E%2E

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(path_is_safe("/%2E%2E/private")).to_equal(false)
```

</details>

### path_is_safe — backslash traversal rejection

#### rejects backslash-dot-dot prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(path_is_safe("\\..\\windows")).to_equal(false)
```

</details>

#### rejects dot-dot-backslash

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(path_is_safe("..\\etc")).to_equal(false)
```

</details>

### path_is_safe — double-slash rejection

#### rejects // at start

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(path_is_safe("//etc/passwd")).to_equal(false)
```

</details>

#### rejects // in middle

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(path_is_safe("/api//secret")).to_equal(false)
```

</details>

### path_is_safe — null byte rejection

#### rejects literal null byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = "/file\0.txt"
expect(path_is_safe(p)).to_equal(false)
```

</details>

#### rejects %00 encoded null

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(path_is_safe("/file%00.txt")).to_equal(false)
```

</details>

### path_is_safe — valid paths accepted

#### accepts root

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(path_is_safe("/")).to_equal(true)
```

</details>

#### accepts normal file path

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(path_is_safe("/static/style.css")).to_equal(true)
```

</details>

#### accepts path with dots in filename

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(path_is_safe("/js/app.min.js")).to_equal(true)
```

</details>

#### accepts path with numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(path_is_safe("/api/v2/users/42")).to_equal(true)
```

</details>

#### accepts path with query-like segment

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(path_is_safe("/search?q=hello")).to_equal(true)
```

</details>

#### accepts single dot segment (current directory reference)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(path_is_safe("/./safe")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
