# Compiler Entrypoint Index Compatibility Specification

> Tests covering entrypoint package-index compatibility markers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compiler Entrypoint Index Compatibility Specification

## Scenarios

### entrypoint package-index compatibility markers

#### should clear earlier compatibility markers when a graph is rejected

- Retain caller environment before testing rejected cache generations
- Reject both an unsupported graph schema and a missing variant
   - Expected: compiler_entrypoint_publish_index_compatibility_v1(graph) is false
   - Expected: env_get("SIMPLE_PACKAGE_INDEX_PRODUCER_DIGEST") ?? "" equals ``
   - Expected: env_get("SIMPLE_PACKAGE_INDEX_ROOT_GENERATION") ?? "" equals ``
   - Expected: env_get("SIMPLE_PACKAGE_INDEX_VARIANT_DIGEST") ?? "" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Retain caller environment before testing rejected cache generations")
val old_producer = env_get("SIMPLE_PACKAGE_INDEX_PRODUCER_DIGEST") ?? ""
val old_root = env_get("SIMPLE_PACKAGE_INDEX_ROOT_GENERATION") ?? ""
val old_variant = env_get("SIMPLE_PACKAGE_INDEX_VARIANT_DIGEST") ?? ""
val digest = sha256_text("rejected-index-compatibility-fixture")
val entry = PackageModuleIndexEntryV1(
    "pkg", "mod", "src/mod.spl", digest, digest, digest, digest,
    digest, digest, digest, digest, "scc", [], [])
step("Reject both an unsupported graph schema and a missing variant")
for schema in [1, 2]:
    env_set("SIMPLE_PACKAGE_INDEX_PRODUCER_DIGEST", digest)
    env_set("SIMPLE_PACKAGE_INDEX_ROOT_GENERATION", "old-root")
    env_set("SIMPLE_PACKAGE_INDEX_VARIANT_DIGEST", digest)
    val graph = PackageModuleIndexGenerationV1(
        schema, digest, "new-root", "revision", "commit", "tree", digest,
        [entry], if schema == 1: digest else: "")
    expect(compiler_entrypoint_publish_index_compatibility_v1(graph)).to_equal(false)
    expect(env_get("SIMPLE_PACKAGE_INDEX_PRODUCER_DIGEST") ?? "").to_equal("")
    expect(env_get("SIMPLE_PACKAGE_INDEX_ROOT_GENERATION") ?? "").to_equal("")
    expect(env_get("SIMPLE_PACKAGE_INDEX_VARIANT_DIGEST") ?? "").to_equal("")
env_set("SIMPLE_PACKAGE_INDEX_PRODUCER_DIGEST", old_producer)
env_set("SIMPLE_PACKAGE_INDEX_ROOT_GENERATION", old_root)
env_set("SIMPLE_PACKAGE_INDEX_VARIANT_DIGEST", old_variant)
```

</details>

#### publishes an admitted graph and clears a later binding-only generation

<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val old_producer = env_get("SIMPLE_PACKAGE_INDEX_PRODUCER_DIGEST") ?? ""
val old_root = env_get("SIMPLE_PACKAGE_INDEX_ROOT_GENERATION") ?? ""
val old_variant = env_get("SIMPLE_PACKAGE_INDEX_VARIANT_DIGEST") ?? ""
val digest = sha256_text("index-compatibility-fixture")
val entry = PackageModuleIndexEntryV1(
    "pkg", "mod", "src/mod.spl", digest, digest, digest, digest,
    digest, digest, digest, digest, "scc", [], [])
val graph = PackageModuleIndexGenerationV1(
    2, digest, "root", "revision", "commit", "tree", digest,
    [entry], digest)
val binding = PackageModuleIndexGenerationV1(
    1, digest, "binding", "revision", "commit", "tree", digest,
    [])

expect(compiler_entrypoint_publish_index_compatibility_v1(graph)).to_equal(true)
expect(env_get("SIMPLE_PACKAGE_INDEX_PRODUCER_DIGEST") ?? "").to_equal(digest)
expect(env_get("SIMPLE_PACKAGE_INDEX_ROOT_GENERATION") ?? "").to_equal("root")
expect(env_get("SIMPLE_PACKAGE_INDEX_VARIANT_DIGEST") ?? "").to_equal(digest)

expect(compiler_entrypoint_publish_index_compatibility_v1(binding)).to_equal(true)
expect(env_get("SIMPLE_PACKAGE_INDEX_PRODUCER_DIGEST") ?? "").to_equal("")
expect(env_get("SIMPLE_PACKAGE_INDEX_ROOT_GENERATION") ?? "").to_equal("")
expect(env_get("SIMPLE_PACKAGE_INDEX_VARIANT_DIGEST") ?? "").to_equal("")
env_set("SIMPLE_PACKAGE_INDEX_PRODUCER_DIGEST", old_producer)
env_set("SIMPLE_PACKAGE_INDEX_ROOT_GENERATION", old_root)
env_set("SIMPLE_PACKAGE_INDEX_VARIANT_DIGEST", old_variant)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/compiler_entrypoint_index_compatibility_spec.spl` |
| Updated | 2026-09-29 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering entrypoint package-index compatibility markers.
- entrypoint package-index compatibility markers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
