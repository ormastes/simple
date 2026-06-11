# Runtime Compiler Specification

> 1. with env

<!-- sdn-diagram:id=runtime_compiler_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=runtime_compiler_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

runtime_compiler_spec -> compiler
runtime_compiler_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=runtime_compiler_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Runtime Compiler Specification

## Scenarios

### Runtime Compiler

#### honors SIMPLE_CC override

1. with env
   - Expected: find_c_compiler() equals `/custom/toolchain/cc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
with_env("SIMPLE_CC", "/custom/toolchain/cc", fn():
    expect(find_c_compiler()).to_equal("/custom/toolchain/cc")
)
```

</details>

#### honors SIMPLE_PROJECT_ROOT override before cwd fallback

1. with env
   - Expected: find_runtime_source_dir() equals `{project_root}/src/runtime`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val project_root = cwd()
with_env("SIMPLE_PROJECT_ROOT", project_root, fn():
    expect(find_runtime_source_dir()).to_equal("{project_root}/src/runtime")
)
```

</details>

#### finds runtime sources from cwd when no override is set

1. with env
   - Expected: find_runtime_source_dir() equals `src/runtime`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
with_env("SIMPLE_PROJECT_ROOT", "", fn():
    expect(find_runtime_source_dir()).to_equal("src/runtime")
)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/runtime_compiler_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Runtime Compiler

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
