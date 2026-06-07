# Module Loader Semantic Cache Specification

> 1. moduleloader record semantic fingerprint

<!-- sdn-diagram:id=module_loader_semantic_cache_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=module_loader_semantic_cache_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

module_loader_semantic_cache_spec -> std
module_loader_semantic_cache_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=module_loader_semantic_cache_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Module Loader Semantic Cache Specification

## Scenarios

### Module loader semantic cache invalidation

#### fails closed when dependency semantic fingerprints change

1. moduleloader record semantic fingerprint

2. moduleloader record dependency semantic fingerprint


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loader = ModuleLoader.with_defaults()
moduleloader_record_semantic_fingerprint(loader, "A.smf", "A:abi:v1")
moduleloader_record_dependency_semantic_fingerprint(loader, "A.smf", "B.smf", "B:field-wrapper:v1")

var deps_v1: Dict<text, text> = {}
deps_v1["B.smf"] = "B:field-wrapper:v1"
expect(moduleloader_semantic_cache_is_fresh(loader, "A.smf", "A:abi:v1", deps_v1)).to_be(true)

var deps_v2: Dict<text, text> = {}
deps_v2["B.smf"] = "B:field-wrapper:v2"
expect(moduleloader_semantic_cache_is_fresh(loader, "A.smf", "A:abi:v1", deps_v2)).to_be(false)
```

</details>

#### finds transitive dependents through dependency cycles

1. moduleloader record semantic fingerprint

2. moduleloader record semantic fingerprint

3. moduleloader record dependency semantic fingerprint

4. moduleloader record dependency semantic fingerprint


<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loader = ModuleLoader.with_defaults()
moduleloader_record_semantic_fingerprint(loader, "A.smf", "A:abi:v1")
moduleloader_record_semantic_fingerprint(loader, "B.smf", "B:abi:v1")
moduleloader_record_dependency_semantic_fingerprint(loader, "A.smf", "B.smf", "B:field-wrapper:v1")
moduleloader_record_dependency_semantic_fingerprint(loader, "B.smf", "A.smf", "A:field-wrapper:v1")

val affected = moduleloader_semantic_dependents_of(loader, "B.smf")
expect(affected.contains("A.smf")).to_be(true)
expect(affected.contains("B.smf")).to_be(true)

val invalidated = moduleloader_invalidate_semantic_change(loader, "B.smf")
expect(invalidated.contains("A.smf")).to_be(true)
expect(invalidated.contains("B.smf")).to_be(true)
expect(moduleloader_semantic_cache_is_fresh(loader, "A.smf", "A:abi:v1", {})).to_be(false)
```

</details>

#### invalidates JIT symbols compiled against a field-wrapper semantic key

1. loader jit set cache for test

2. loader jit set symbol semantic keys


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loader = ModuleLoader.with_defaults()
val symbol_name = "Vec$field_wrapper"
loader.jit.set_cache_for_test(symbol_name, [1, 2, 3], 4096)
loader.jit.set_symbol_semantic_keys(symbol_name, ["B.value.field_wrapper"])

expect(loader.jit.jit_cache.has(symbol_name)).to_be(true)

val removed = loader.jit.invalidate_by_semantic_key("B.value.field_wrapper")

expect(removed.contains(symbol_name)).to_be(true)
expect(loader.jit.jit_cache.has(symbol_name)).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/loader/module_loader_semantic_cache_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Module loader semantic cache invalidation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
