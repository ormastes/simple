# Driver Api Tier Policy Specification

> <details>

<!-- sdn-diagram:id=driver_api_tier_policy_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=driver_api_tier_policy_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

driver_api_tier_policy_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=driver_api_tier_policy_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Driver Api Tier Policy Specification

## Scenarios

### Driver API Tier Policy Guardrails

#### tier 0 driver_api_types has no compiler graph imports

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = read_file("src/compiler/80.driver/driver_api_types.spl")
val heavy_imports = [
    "compiler.hir", "compiler.mir", "compiler.backend",
    "compiler.frontend", "compiler.types", "compiler.mono",
    "compiler.borrow", "compiler.semantics", "compiler.tools",
    "compiler.mir_opt", "CompilerDriver"
]
var i = 0
while i < heavy_imports.len():
    expect(contains_import_line(content, heavy_imports[i])).to_equal(false)
    i = i + 1
```

</details>

#### tier 0 driver_api_types exports find_runtime_lib_dir

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/80.driver/driver_api_types.spl") ?? ""
expect(contains_line(content, "export find_runtime_lib_dir")).to_equal(true)
```

</details>

#### facade driver_api does not import from driver_api_core

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/80.driver/driver_api.spl") ?? ""
expect(contains_import_line(content, "driver_api_core")).to_equal(false)
```

</details>

#### facade driver_api delegates to lightweight public modules

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/80.driver/driver_api.spl") ?? ""
expect(contains_line(content, "driver_public_compile")).to_equal(true)
expect(contains_line(content, "driver_public_api")).to_equal(true)
expect(contains_line(content, "driver_public_shared")).to_equal(true)
```

</details>

#### driver __init__.spl uses explicit export use statements

<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/80.driver/__init__.spl") ?? ""
val lines = content.split("\n")
val allowed_shared_exports = [
    "export compiler_shared.backend.*",
    "export compiler_shared.blocks.*",
    "export compiler_shared.type_system.*",
    "export compiler_shared.hir.*",
    "export compiler_shared.mir.*",
    "export compiler_shared.error_explanations.*",
    "export compiler_shared.pattern_analysis.*",
    "export compiler_shared.semantics.*"
]
var unexpected_bare_export_count = 0
var i = 0
while i < lines.len():
    val line = lines[i].trim()
    if line != "" and not line.starts_with("#") and line.starts_with("export "):
        var matched_allowed = false
        var j = 0
        while j < allowed_shared_exports.len():
            if line == allowed_shared_exports[j]:
                matched_allowed = true
                break
            j = j + 1
        if not matched_allowed and not line.starts_with("export use "):
            unexpected_bare_export_count = unexpected_bare_export_count + 1
    i = i + 1
expect(unexpected_bare_export_count).to_equal(0)
expect(count_exact_lines(content, allowed_shared_exports)).to_equal(allowed_shared_exports.len())
```

</details>

#### tier 1 driver_api_interpret does not import from tier 2+

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/80.driver/driver_api_interpret.spl") ?? ""
val forbidden = [
    "driver_api_compile_single", "driver_api_codegen_backends",
    "driver_api_native_single", "driver_api_project_build"
]
var i = 0
while i < forbidden.len():
    expect(contains_import_line(content, forbidden[i])).to_equal(false)
    i = i + 1
```

</details>

#### tier 2 driver_api_compile_single does not import from tier 3+

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/80.driver/driver_api_compile_single.spl") ?? ""
val forbidden = [
    "driver_api_codegen_backends", "driver_api_native_single",
    "driver_api_project_build"
]
var i = 0
while i < forbidden.len():
    expect(contains_import_line(content, forbidden[i])).to_equal(false)
    i = i + 1
```

</details>

#### tier 3 driver_api_codegen_backends does not import from tier 4+

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/80.driver/driver_api_codegen_backends.spl") ?? ""
val forbidden = ["driver_api_native_single", "driver_api_project_build"]
var i = 0
while i < forbidden.len():
    expect(contains_import_line(content, forbidden[i])).to_equal(false)
    i = i + 1
```

</details>

#### tier 4 driver_api_native_single does not import from tier 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/80.driver/driver_api_native_single.spl") ?? ""
expect(contains_import_line(content, "driver_api_project_build")).to_equal(false)
```

</details>

#### driver_api_core re-exports from all 6 tiers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/80.driver/driver_api_core.spl") ?? ""
expect(contains_import_line(content, "driver_api_types")).to_equal(true)
expect(contains_import_line(content, "driver_api_interpret")).to_equal(true)
expect(contains_import_line(content, "driver_api_compile_single")).to_equal(true)
expect(contains_import_line(content, "driver_api_codegen_backends")).to_equal(true)
expect(contains_import_line(content, "driver_api_native_single")).to_equal(true)
expect(contains_import_line(content, "driver_api_project_build")).to_equal(true)
```

</details>

#### driver_api_core is a thin re-export file under 25 lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/80.driver/driver_api_core.spl") ?? ""
val lines = content.split("\n")
expect(lines.len() < 25).to_equal(true)
```

</details>

#### 50.mir __init__.spl has no bare exports

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/50.mir/__init__.spl") ?? ""
val lines = content.split("\n")
var bare_count = 0
var i = 0
while i < lines.len():
    val line = lines[i].trim()
    if line.starts_with("export ") and not line.starts_with("export use ") and not line.starts_with("#"):
        bare_count = bare_count + 1
    i = i + 1
expect(bare_count).to_equal(0)
```

</details>

#### 20.hir __init__.spl has no bare exports

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/20.hir/__init__.spl") ?? ""
val lines = content.split("\n")
var bare_count = 0
var i = 0
while i < lines.len():
    val line = lines[i].trim()
    if line.starts_with("export ") and not line.starts_with("export use ") and not line.starts_with("#"):
        bare_count = bare_count + 1
    i = i + 1
expect(bare_count).to_equal(0)
```

</details>

#### 25.traits __init__.spl has no bare exports

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/25.traits/__init__.spl") ?? ""
val lines = content.split("\n")
var bare_count = 0
var i = 0
while i < lines.len():
    val line = lines[i].trim()
    if line.starts_with("export ") and not line.starts_with("export use ") and not line.starts_with("#"):
        bare_count = bare_count + 1
    i = i + 1
expect(bare_count).to_equal(0)
```

</details>

#### 35.semantics __init__.spl has no bare exports

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/35.semantics/__init__.spl") ?? ""
val lines = content.split("\n")
var bare_count = 0
var i = 0
while i < lines.len():
    val line = lines[i].trim()
    if line.starts_with("export ") and not line.starts_with("export use ") and not line.starts_with("#"):
        bare_count = bare_count + 1
    i = i + 1
expect(bare_count).to_equal(0)
```

</details>

#### 40.mono __init__.spl has no bare exports

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/40.mono/__init__.spl") ?? ""
val lines = content.split("\n")
var bare_count = 0
var i = 0
while i < lines.len():
    val line = lines[i].trim()
    if line.starts_with("export ") and not line.starts_with("export use ") and not line.starts_with("#"):
        bare_count = bare_count + 1
    i = i + 1
expect(bare_count).to_equal(0)
```

</details>

#### 60.mir_opt __init__.spl has no bare exports

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/60.mir_opt/__init__.spl") ?? ""
val lines = content.split("\n")
var bare_count = 0
var i = 0
while i < lines.len():
    val line = lines[i].trim()
    if line.starts_with("export ") and not line.starts_with("export use ") and not line.starts_with("#"):
        bare_count = bare_count + 1
    i = i + 1
expect(bare_count).to_equal(0)
```

</details>

#### 85.mdsoc __init__.spl has no bare exports

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/85.mdsoc/__init__.spl") ?? ""
val lines = content.split("\n")
var bare_count = 0
var i = 0
while i < lines.len():
    val line = lines[i].trim()
    if line.starts_with("export ") and not line.starts_with("export use ") and not line.starts_with("#"):
        bare_count = bare_count + 1
    i = i + 1
expect(bare_count).to_equal(0)
```

</details>

#### 90.tools __init__.spl has no bare exports

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/90.tools/__init__.spl") ?? ""
val lines = content.split("\n")
var bare_count = 0
var i = 0
while i < lines.len():
    val line = lines[i].trim()
    if line.starts_with("export ") and not line.starts_with("export use ") and not line.starts_with("#"):
        bare_count = bare_count + 1
    i = i + 1
expect(bare_count).to_equal(0)
```

</details>

#### 99.loader __init__.spl has no bare exports

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/99.loader/__init__.spl") ?? ""
val lines = content.split("\n")
var bare_count = 0
var i = 0
while i < lines.len():
    val line = lines[i].trim()
    if line.starts_with("export ") and not line.starts_with("export use ") and not line.starts_with("#"):
        bare_count = bare_count + 1
    i = i + 1
expect(bare_count).to_equal(0)
```

</details>

#### driver_core_types canonical source is in compiler.common

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/00.common/driver_core_types.spl") ?? ""
expect(contains_line(content, "enum CompileMode")).to_equal(true)
expect(contains_line(content, "enum CompileResult")).to_equal(true)
expect(contains_line(content, "struct CompileOptions")).to_equal(true)
```

</details>

#### driver_core_types shim in 80.driver re-exports from compiler.common

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/80.driver/driver_core_types.spl") ?? ""
expect(contains_import_line(content, "compiler.common.driver_core_types")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/driver_api_tier_policy_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Driver API Tier Policy Guardrails

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
