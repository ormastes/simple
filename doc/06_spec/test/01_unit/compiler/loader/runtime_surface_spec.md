# Runtime Surface Specification

> <details>

<!-- sdn-diagram:id=runtime_surface_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=runtime_surface_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

runtime_surface_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=runtime_surface_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Runtime Surface Specification

## Scenarios

### loader runtime compatibility surfaces

#### loader alias package is a thin alias to the curated runtime package

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val alias_text = loader_alias_init_text()
expect(alias_text).to_contain("export use compiler.loader.runtime.*")
expect(alias_text.contains("export ModuleLoader")).to_equal(false)
expect(alias_text.contains("export native_mmap_file")).to_equal(false)
```

</details>

#### runtime facade keeps the curated export list and avoids duplicate jit-context instantiation exports

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runtime_text = runtime_init_text()
expect(runtime_text).to_contain("export JitCompilationContext")
expect(runtime_text).to_contain("export InstantiationRecord")
expect(runtime_text.contains("# Re-exported from jit_context.spl\nexport JitCompilationContext\nexport InstantiationRecord")).to_equal(false)
```

</details>

#### root compatibility facade still documents compiler.loader.runtime as the preferred public surface

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root_text = root_loader_init_text()
expect(root_text).to_contain("compiler.loader.runtime")
expect(root_text).to_contain("moduleloader_load")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/loader/runtime_surface_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- loader runtime compatibility surfaces

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
