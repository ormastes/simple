# Native Backend Coverage Specification

> <details>

<!-- sdn-diagram:id=native_backend_coverage_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_backend_coverage_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_backend_coverage_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_backend_coverage_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Backend Coverage Specification

## Scenarios

### Native Backend Coverage

#### check_coverage API returns valid result for native compile line coverage

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = check_coverage("line", "src/app/compile/native.spl", minimum: 0.0)
expect(result.coverage_type).to_equal("line")
print "  native.spl line coverage: {result.actual}%  files_matched={result.files_matched}"
```

</details>

#### check_coverage API returns valid result for native compile branch coverage

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = check_coverage("branch", "src/app/compile/native.spl", minimum: 0.0)
expect(result.coverage_type).to_equal("branch")
print "  native.spl branch coverage: {result.actual}%  files_matched={result.files_matched}"
```

</details>

#### check_coverage API returns valid result for llvm direct line coverage

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = check_coverage("line", "src/app/compile/llvm_direct.spl", minimum: 0.0)
expect(result.coverage_type).to_equal("line")
print "  llvm_direct.spl line coverage: {result.actual}%  files_matched={result.files_matched}"
```

</details>

#### check_coverage API returns valid result for wildcard compile pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = check_coverage("line", "src/app/compile/**", minimum: 0.0)
expect(result.coverage_type).to_equal("line")
print "  src/app/compile/** line coverage: {result.actual}%  files_matched={result.files_matched}"
```

</details>

#### coverage_type and pattern are preserved on result

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = check_coverage("function", "src/app/compile/native.spl", minimum: 0.0)
expect(result.coverage_type).to_equal("function")
expect(result.pattern).to_equal("src/app/compile/native.spl")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/native_backend_coverage_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Native Backend Coverage

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
