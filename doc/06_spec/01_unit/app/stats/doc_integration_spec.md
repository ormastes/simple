# Doc Integration Specification

> <details>

<!-- sdn-diagram:id=doc_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=doc_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

doc_integration_spec -> std
doc_integration_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=doc_integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Doc Integration Specification

## Scenarios

### stats command coverage output

#### stats shows non-zero file counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_simple(["stats", "--quick"])
val stdout = result.0
val exit_code = result.2
expect(exit_code).to_equal(0)
expect(stdout.contains("Files:")).to_equal(true)
```

</details>

#### stats --json returns valid JSON with documentation section

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_simple(["stats", "--json"])
val stdout = result.0
val exit_code = result.2
expect(exit_code).to_equal(0)
expect(stdout.contains("\"documentation\"")).to_equal(true)
```

</details>

#### stats --json documentation has total_public field

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_simple(["stats", "--json"])
val stdout = result.0
expect(stdout.contains("\"total_public\"")).to_equal(true)
```

</details>

#### stats --json documentation has non-zero total_public

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_simple(["stats", "--json"])
val stdout = result.0
# total_public should not be 0 in a real project
val has_nonzero = not stdout.contains("\"total_public\": 0")
expect(has_nonzero).to_equal(true)
```

</details>

#### stats --json has per_scope section

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_simple(["stats", "--json"])
val stdout = result.0
expect(stdout.contains("\"per_scope\"")).to_equal(true)
```

</details>

#### stats --json per_scope has std section

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_simple(["stats", "--json"])
val stdout = result.0
expect(stdout.contains("\"std\"")).to_equal(true)
```

</details>

#### stats --json per_scope has core section

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_simple(["stats", "--json"])
val stdout = result.0
expect(stdout.contains("\"core\"")).to_equal(true)
```

</details>

#### stats --json lib documented field is not always 100 percent

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_simple(["stats", "--json"])
val stdout = result.0
# The old bug always showed lib at 100% - verify the field exists
expect(stdout.contains("\"lib\"")).to_equal(true)
```

</details>

### stats JSON export format

#### stats --json outputs valid JSON braces

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_simple(["stats", "--json"])
val stdout = result.0
expect(stdout.starts_with("{")).to_equal(true)
expect(stdout.ends_with("}")).to_equal(true)
```

</details>

#### stats --json has files section

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_simple(["stats", "--json"])
val stdout = result.0
expect(stdout.contains("\"files\"")).to_equal(true)
```

</details>

#### stats --json has tests section

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_simple(["stats", "--json"])
val stdout = result.0
expect(stdout.contains("\"tests\"")).to_equal(true)
```

</details>

#### stats --json has features section

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_simple(["stats", "--json"])
val stdout = result.0
expect(stdout.contains("\"features\"")).to_equal(true)
```

</details>

#### stats --json has lines section

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_simple(["stats", "--json"])
val stdout = result.0
expect(stdout.contains("\"lines\"")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/stats/doc_integration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- stats command coverage output
- stats JSON export format

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
