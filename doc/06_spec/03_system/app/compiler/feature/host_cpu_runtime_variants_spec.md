# Host Cpu Runtime Variants Specification

> <details>

<!-- sdn-diagram:id=host_cpu_runtime_variants_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=host_cpu_runtime_variants_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

host_cpu_runtime_variants_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=host_cpu_runtime_variants_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Host Cpu Runtime Variants Specification

## Scenarios

### Host CPU runtime variants

### REQ-001 through REQ-006: strongest executable black-box coverage currently reachable from SPipe

#### passes the targeted simple-simd host-config regression suite

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target_dir = _tmp_target_dir("simd")
val command = "cd '{_repo_root()}' && CARGO_TARGET_DIR='{target_dir}' CARGO_NET_OFFLINE=true cargo test -p simple-simd --lib --offline"
val result = _run_shell(command)

val combined = result.stdout + "\n" + result.stderr
expect(result.exit_code).to_equal(0)
expect(combined.contains("writes_and_reads_cpu_config_round_trip")).to_equal(true)
expect(combined.contains("clamps_invalid_enabled_values_and_rewrites_file")).to_equal(true)
expect(combined.contains("cpu_config_path_honors_trimmed_override")).to_equal(true)
expect(combined.contains("active_simd_tier_prefers_env_override_over_config")).to_equal(true)
expect(combined.contains("host_cpu_config_reloads_after_on_disk_edit_in_same_process")).to_equal(true)
expect(combined.contains("canonical_rewrite_uses_simple_supported_intersection")).to_equal(true)
```

</details>

#### models invalid override fallback when no direct Simple hook can observe it

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_active_tier_model("definitely-not-a-tier", "scalar", "x86_64_avx2")).to_equal("scalar")
```

</details>

### REQ-007 through REQ-013: contract-model coverage for still-unobservable internals

#### keeps only support intersect simple_support in canonical order

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val clamped = _clamp_instruction_sets(
    ["sse2", "avx2", "avx512f"],
    ["sse2", "avx2"],
    ["avx2", "sse2", "avx512f"]
)
expect(clamped.len()).to_equal(2)
expect(clamped[0]).to_equal("sse2")
expect(clamped[1]).to_equal("avx2")
```

</details>

#### probes compatible sibling runtime variants before the scalar fallback

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val candidates = _runtime_library_candidates("", "x86_64_avx512")
expect(candidates.len()).to_equal(3)
expect(candidates[0]).to_equal("libsimple_runtime.x86_64_avx2.so")
expect(candidates[1]).to_equal("libsimple_runtime.x86_64_sse2.so")
expect(candidates[2]).to_equal("libsimple_runtime.so")
```

</details>

#### keeps explicit-path probes in the sibling directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val candidates = _runtime_library_candidates("/tmp/runtime", "aarch64_sve2")
expect(candidates.len()).to_equal(2)
expect(candidates[0]).to_equal("/tmp/runtime/libsimple_runtime.aarch64_neon.so")
expect(candidates[1]).to_equal("/tmp/runtime/libsimple_runtime.so")
```

</details>

#### falls through lower compatible embedded variants until a present resource is found

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val selected = _select_embedded_runtime_resource(
    "x86_64_avx512",
    ["x86_64_avx2", "x86_64_sse2", "scalar"],
    ["runtime/avx2.so", "runtime/sse2.so", "runtime/scalar.so"],
    ["runtime/sse2.so", "runtime/scalar.so"]
)
expect(selected).to_equal("runtime/sse2.so")
```

</details>

#### fails closed when manifest metadata is truncated or malformed

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_manifest_is_valid(true, false, true)).to_equal(false)
expect(_manifest_is_valid(true, true, false)).to_equal(false)
expect(_manifest_is_valid(false, false, false)).to_equal(true)
```

</details>

#### changes cache identity when the active tier changes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scalar_key = _cache_identity("object:main", "scalar")
val sse2_key = _cache_identity("object:main", "x86_64_sse2")
expect(scalar_key == sse2_key).to_equal(false)
```

</details>

#### changes stdlib root ordering when the configured tier changes

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scalar_roots = _stdlib_root_candidates("src/lib/std/src", "scalar")
val sse2_roots = _stdlib_root_candidates("src/lib/std/src", "x86_64_sse2")
expect(scalar_roots.len()).to_equal(1)
expect(scalar_roots[0]).to_equal("src/lib/std/src")
expect(sse2_roots.len()).to_equal(2)
expect(sse2_roots[0]).to_equal("src/lib/std/variants/x86_64_sse2/src")
expect(sse2_roots[1]).to_equal("src/lib/std/src")
```

</details>

#### collapses higher x86 tiers to implemented v1 runtime artifacts

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x86 = _implemented_fallback_tiers("x86_64_avx512")
expect(x86.len()).to_equal(3)
expect(x86[0]).to_equal("x86_64_avx2")
expect(x86[1]).to_equal("x86_64_sse2")
expect(x86[2]).to_equal("scalar")
```

</details>

#### collapses SVE and SVE2 hosts through neon before scalar

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sve2 = _implemented_fallback_tiers("aarch64_sve2")
val sve = _implemented_fallback_tiers("aarch64_sve")
expect(sve2.len()).to_equal(2)
expect(sve2[0]).to_equal("aarch64_neon")
expect(sve2[1]).to_equal("scalar")
expect(sve[0]).to_equal("aarch64_neon")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/compiler/feature/host_cpu_runtime_variants_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Host CPU runtime variants
- REQ-001 through REQ-006: strongest executable black-box coverage currently reachable from SPipe
- REQ-007 through REQ-013: contract-model coverage for still-unobservable internals

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
