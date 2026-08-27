# Index Module Unit Tests

> Unit tests for the registry index parser and query functions.

<!-- sdn-diagram:id=index_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=index_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

index_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=index_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Index Module Unit Tests

Unit tests for the registry index parser and query functions.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Tooling |
| Status | In Progress |
| Source | `test/01_unit/app/package/index_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Unit tests for the registry index parser and query functions.

## Scenarios

### index_path_for

#### handles standard 4+ char names

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = index_path_for("http")
expect(path).to_equal("ht/tp/http.sdn")
```

</details>

#### handles 3 char names

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = index_path_for("url")
expect(path).to_equal("ur/l/url.sdn")
```

</details>

#### handles 2 char names

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = index_path_for("io")
expect(path).to_equal("i/o/io.sdn")
```

</details>

#### handles 1 char names

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = index_path_for("x")
expect(path).to_equal("_/x/x.sdn")
```

</details>

#### handles long names

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = index_path_for("collections")
expect(path).to_equal("co/ll/collections.sdn")
```

</details>

### parse_token_from_sdn

#### extracts token from credentials file

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "registry:\n  token: ghp-abc123\n  type: github_pat\n"
val token = parse_token("token:", content)
expect(token).to_equal("ghp-abc123")
```

</details>

#### returns empty for missing token

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "registry:\n  type: github_pat\n"
val token = parse_token("token:", content)
expect(token).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
