# Module Loader Coverage Specification

> <details>

<!-- sdn-diagram:id=module_loader_coverage_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=module_loader_coverage_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

module_loader_coverage_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=module_loader_coverage_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Module Loader Coverage Specification

## Scenarios

### Module Loader Coverage

#### check_coverage API returns valid result for loader line coverage

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = check_coverage("line", "src/core/interpreter/module_loader.spl", minimum: 0.0)
expect(result.coverage_type).to_equal("line")
print "  module_loader.spl line coverage: {result.actual}%  files_matched={result.files_matched}"
```

</details>

#### check_coverage API returns valid result for loader branch coverage

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = check_coverage("branch", "src/core/interpreter/module_loader.spl", minimum: 0.0)
expect(result.coverage_type).to_equal("branch")
print "  module_loader.spl branch coverage: {result.actual}%  files_matched={result.files_matched}"
```

</details>

#### check_coverage API returns valid result for loader function coverage

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = check_coverage("function", "src/core/interpreter/module_loader.spl", minimum: 0.0)
expect(result.coverage_type).to_equal("function")
print "  module_loader.spl function coverage: {result.actual}%  files_matched={result.files_matched}"
```

</details>

#### check_coverage API returns valid result for wildcard loader pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = check_coverage("line", "src/core/interpreter/**", minimum: 0.0)
expect(result.coverage_type).to_equal("line")
print "  src/core/interpreter/** line coverage: {result.actual}%  files_matched={result.files_matched}"
```

</details>

#### coverage_type field is preserved on error result

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = check_coverage("branch", "src/core/interpreter/module_loader.spl", minimum: 0.0)
expect(result.coverage_type).to_equal("branch")
expect(result.pattern).to_equal("src/core/interpreter/module_loader.spl")
```

</details>

#### minimum_check field is set correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = check_coverage("line", "src/core/interpreter/module_loader.spl", minimum: 0.0, minimum_check: true)
expect(result.minimum_check).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/module_import/module_loader_coverage_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Module Loader Coverage

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
