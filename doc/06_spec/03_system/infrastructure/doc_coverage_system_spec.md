# Doc Coverage System Specification

> <details>

<!-- sdn-diagram:id=doc_coverage_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=doc_coverage_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

doc_coverage_system_spec -> std
doc_coverage_system_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=doc_coverage_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Doc Coverage System Specification

## Scenarios

### doc-coverage CLI - terminal mode

<details>
<summary>Advanced: doc-coverage exits with 0</summary>

#### doc-coverage exits with 0 _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_simple(["doc-coverage"])
val exit_code = result.2
expect(exit_code).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: doc-coverage shows coverage report header</summary>

#### doc-coverage shows coverage report header _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_simple(["doc-coverage"])
val stdout = result.0
expect(stdout.contains("Coverage Report")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: doc-coverage shows non-zero public function count</summary>

#### doc-coverage shows non-zero public function count _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_simple(["doc-coverage"])
val stdout = result.0
expect(stdout.contains("Public Functions:")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: doc-coverage shows per-scope breakdown</summary>

#### doc-coverage shows per-scope breakdown _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_simple(["doc-coverage"])
val stdout = result.0
expect(stdout.contains("Per-Scope Breakdown")).to_equal(true)
```

</details>


</details>

### doc-coverage CLI - JSON mode

<details>
<summary>Advanced: doc-coverage --format=json exits with 0</summary>

#### doc-coverage --format=json exits with 0 _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_simple(["doc-coverage", "--format=json"])
val exit_code = result.2
expect(exit_code).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: doc-coverage --format=json outputs JSON</summary>

#### doc-coverage --format=json outputs JSON _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_simple(["doc-coverage", "--format=json"])
val stdout = result.0
expect(stdout.starts_with("{")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: doc-coverage --format=json has total_public field</summary>

#### doc-coverage --format=json has total_public field _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_simple(["doc-coverage", "--format=json"])
val stdout = result.0
expect(stdout.contains("\"total_public\"")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: doc-coverage --format=json has per_scope field</summary>

#### doc-coverage --format=json has per_scope field _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_simple(["doc-coverage", "--format=json"])
val stdout = result.0
expect(stdout.contains("\"per_scope\"")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: doc-coverage --format=json total_public is non-zero</summary>

#### doc-coverage --format=json total_public is non-zero _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_simple(["doc-coverage", "--format=json"])
val stdout = result.0
val has_nonzero = not stdout.contains("\"total_public\": 0")
expect(has_nonzero).to_equal(true)
```

</details>


</details>

### doc-coverage CLI - Markdown mode

<details>
<summary>Advanced: doc-coverage --format=md exits with 0</summary>

#### doc-coverage --format=md exits with 0 _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_simple(["doc-coverage", "--format=md"])
val exit_code = result.2
expect(exit_code).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: doc-coverage --format=md outputs markdown heading</summary>

#### doc-coverage --format=md outputs markdown heading _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_simple(["doc-coverage", "--format=md"])
val stdout = result.0
expect(stdout.contains("# Documentation Coverage Report")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: doc-coverage --format=md contains table</summary>

#### doc-coverage --format=md contains table _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_simple(["doc-coverage", "--format=md"])
val stdout = result.0
expect(stdout.contains("|")).to_equal(true)
```

</details>


</details>

### doc-coverage CLI - missing flag

<details>
<summary>Advanced: doc-coverage --missing exits with 0</summary>

#### doc-coverage --missing exits with 0 _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_simple(["doc-coverage", "--missing"])
val exit_code = result.2
expect(exit_code).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: doc-coverage --missing shows undocumented header</summary>

#### doc-coverage --missing shows undocumented header _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_simple(["doc-coverage", "--missing"])
val stdout = result.0
expect(stdout.contains("Undocumented")).to_equal(true)
```

</details>


</details>

### doc-coverage CLI - path scoping

<details>
<summary>Advanced: doc-coverage src/core scopes to core</summary>

#### doc-coverage src/core scopes to core _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_simple(["doc-coverage", "src/core"])
val stdout = result.0
val exit_code = result.2
expect(exit_code).to_equal(0)
expect(stdout.contains("src/core")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: doc-coverage src/std scopes to std</summary>

#### doc-coverage src/std scopes to std _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_simple(["doc-coverage", "src/std"])
val stdout = result.0
val exit_code = result.2
expect(exit_code).to_equal(0)
expect(stdout.contains("src/std")).to_equal(true)
```

</details>


</details>

### stats command coverage integration

<details>
<summary>Advanced: stats shows Coverage section with non-zero values</summary>

#### stats shows Coverage section with non-zero values _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_simple(["doc-coverage"])
val stdout = result.0
val exit_code = result.2
expect(exit_code).to_equal(0)
expect(stdout.contains("Documentation Coverage Report")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: stats --json documentation total_public is non-zero</summary>

#### stats --json documentation total_public is non-zero _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_simple(["doc-coverage", "--format=json"])
val stdout = result.0
val has_nonzero = not stdout.contains("\"total_public\": 0")
expect(has_nonzero).to_equal(true)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/infrastructure/doc_coverage_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- doc-coverage CLI - terminal mode
- doc-coverage CLI - JSON mode
- doc-coverage CLI - Markdown mode
- doc-coverage CLI - missing flag
- doc-coverage CLI - path scoping
- stats command coverage integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 18 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
