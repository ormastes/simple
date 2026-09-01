# Host Cpu Runtime Variants Specification

> Tests covering Host CPU runtime variants, REQ-001 through REQ-006: strongest executable black-box coverage currently reachable from SPipe, REQ-007 through REQ-013: contract-model coverage for still-unobservable internals.

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

- passes the targeted simple-simd host-config regression suite
   - Expected: result.exit_code equals `0`
   - Expected: combined contains `writes_and_reads_cpu_config_round_trip`
   - Expected: combined contains `clamps_invalid_enabled_values_and_rewrites_file`
   - Expected: combined contains `cpu_config_path_honors_trimmed_override`
   - Expected: combined contains `active_simd_tier_prefers_env_override_over_config`
   - Expected: combined contains `host_cpu_config_reloads_after_on_disk_edit_in_same_process`
   - Expected: combined contains `canonical_rewrite_uses_simple_supported_intersection`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-001
# @req REQ-006
# @req REQ-007
# @req REQ-013
# @req REQ-SSPEC-SYSTEM
step("passes the targeted simple-simd host-config regression suite")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val target_dir = _tmp_target_dir("simd")
val command = "cd '{_repo_root()}' && CARGO_TARGET_DIR='{target_dir}' CARGO_NET_OFFLINE=true cargo test -p simple-simd --lib --offline"
val result = _run_shell(command)

val combined = result.stdout + "\n" + result.stderr
expect(result.exit_code).to_equal(0)  # oracle: result.exit_code must equal 0 — authoritative contract constant
expect(combined.contains("writes_and_reads_cpu_config_round_trip")).to_equal(true)
expect(combined.contains("clamps_invalid_enabled_values_and_rewrites_file")).to_equal(true)
expect(combined.contains("cpu_config_path_honors_trimmed_override")).to_equal(true)
expect(combined.contains("active_simd_tier_prefers_env_override_over_config")).to_equal(true)
expect(combined.contains("host_cpu_config_reloads_after_on_disk_edit_in_same_process")).to_equal(true)
expect(combined.contains("canonical_rewrite_uses_simple_supported_intersection")).to_equal(true)
```

</details>

#### models invalid override fallback when no direct Simple hook can observe it

- models invalid override fallback when no direct Simple hook can observe it
   - Expected: _active_tier_model("definitely-not-a-tier", "scalar", "x86_64_avx2") equals `scalar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("models invalid override fallback when no direct Simple hook can observe it")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
expect(_active_tier_model("definitely-not-a-tier", "scalar", "x86_64_avx2")).to_equal("scalar")
```

</details>

### REQ-007 through REQ-013: contract-model coverage for still-unobservable internals

#### keeps only support intersect simple_support in canonical order

- keeps only support intersect simple_support in canonical order
   - Expected: clamped.len() equals `2`
   - Expected: clamped[0] equals `sse2`
   - Expected: clamped[1] equals `avx2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps only support intersect simple_support in canonical order")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val clamped = _clamp_instruction_sets(
    ["sse2", "avx2", "avx512f"],
    ["sse2", "avx2"],
    ["avx2", "sse2", "avx512f"]
)
expect(clamped.len()).to_equal(2)  # oracle: clamped.len() must equal 2 — authoritative contract constant
expect(clamped[0]).to_equal("sse2")
expect(clamped[1]).to_equal("avx2")
```

</details>

#### probes compatible sibling runtime variants before the scalar fallback

- probes compatible sibling runtime variants before the scalar fallback
   - Expected: candidates.len() equals `3`
   - Expected: candidates[0] equals `libsimple_runtime.x86_64_avx2.so`
   - Expected: candidates[1] equals `libsimple_runtime.x86_64_sse2.so`
   - Expected: candidates[2] equals `libsimple_runtime.so`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("probes compatible sibling runtime variants before the scalar fallback")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val candidates = _runtime_library_candidates("", "x86_64_avx512")
expect(candidates.len()).to_equal(3)  # oracle: candidates.len() must equal 3 — authoritative contract constant
expect(candidates[0]).to_equal("libsimple_runtime.x86_64_avx2.so")
expect(candidates[1]).to_equal("libsimple_runtime.x86_64_sse2.so")
expect(candidates[2]).to_equal("libsimple_runtime.so")
```

</details>

#### keeps explicit-path probes in the sibling directory

- keeps explicit-path probes in the sibling directory
   - Expected: candidates.len() equals `2`
   - Expected: candidates[0] equals `/tmp/runtime/libsimple_runtime.aarch64_neon.so`
   - Expected: candidates[1] equals `/tmp/runtime/libsimple_runtime.so`

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
# @req REQ-SSPEC-SYSTEM
step("keeps explicit-path probes in the sibling directory")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val candidates = _runtime_library_candidates("/tmp/runtime", "aarch64_sve2")
expect(candidates.len()).to_equal(2)  # oracle: candidates.len() must equal 2 — authoritative contract constant
expect(candidates[0]).to_equal("/tmp/runtime/libsimple_runtime.aarch64_neon.so")
expect(candidates[1]).to_equal("/tmp/runtime/libsimple_runtime.so")
```

</details>

#### falls through lower compatible embedded variants until a present resource is found

- falls through lower compatible embedded variants until a present resource is found
   - Expected: selected equals `runtime/sse2.so`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("falls through lower compatible embedded variants until a present resource is found")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
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

- fails closed when manifest metadata is truncated or malformed
   - Expected: _manifest_is_valid(true, false, true) is false
   - Expected: _manifest_is_valid(true, true, false) is false
   - Expected: _manifest_is_valid(false, false, false) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fails closed when manifest metadata is truncated or malformed")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
expect(_manifest_is_valid(true, false, true)).to_equal(false)
expect(_manifest_is_valid(true, true, false)).to_equal(false)
expect(_manifest_is_valid(false, false, false)).to_equal(true)
```

</details>

#### changes cache identity when the active tier changes

- changes cache identity when the active tier changes


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("changes cache identity when the active tier changes")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val scalar_key = _cache_identity("object:main", "scalar")
val sse2_key = _cache_identity("object:main", "x86_64_sse2")
expect(scalar_key == sse2_key).to_equal(false)
```

</details>

#### changes stdlib root ordering when the configured tier changes

- changes stdlib root ordering when the configured tier changes
   - Expected: scalar_roots.len() equals `1`
   - Expected: scalar_roots[0] equals `src/lib/std/src`
   - Expected: sse2_roots.len() equals `2`
   - Expected: sse2_roots[0] equals `src/lib/std/variants/x86_64_sse2/src`
   - Expected: sse2_roots[1] equals `src/lib/std/src`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("changes stdlib root ordering when the configured tier changes")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val scalar_roots = _stdlib_root_candidates("src/lib/std/src", "scalar")
val sse2_roots = _stdlib_root_candidates("src/lib/std/src", "x86_64_sse2")
expect(scalar_roots.len()).to_equal(1)  # oracle: scalar_roots.len() must equal 1 — authoritative contract constant
expect(scalar_roots[0]).to_equal("src/lib/std/src")
expect(sse2_roots.len()).to_equal(2)  # oracle: sse2_roots.len() must equal 2 — authoritative contract constant
expect(sse2_roots[0]).to_equal("src/lib/std/variants/x86_64_sse2/src")
expect(sse2_roots[1]).to_equal("src/lib/std/src")
```

</details>

#### collapses higher x86 tiers to implemented v1 runtime artifacts

- collapses higher x86 tiers to implemented v1 runtime artifacts
   - Expected: x86.len() equals `3`
   - Expected: x86[0] equals `x86_64_avx2`
   - Expected: x86[1] equals `x86_64_sse2`
   - Expected: x86[2] equals `scalar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("collapses higher x86 tiers to implemented v1 runtime artifacts")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val x86 = _implemented_fallback_tiers("x86_64_avx512")
expect(x86.len()).to_equal(3)  # oracle: x86.len() must equal 3 — authoritative contract constant
expect(x86[0]).to_equal("x86_64_avx2")
expect(x86[1]).to_equal("x86_64_sse2")
expect(x86[2]).to_equal("scalar")
```

</details>

#### collapses SVE and SVE2 hosts through neon before scalar

- collapses SVE and SVE2 hosts through neon before scalar
   - Expected: sve2.len() equals `2`
   - Expected: sve2[0] equals `aarch64_neon`
   - Expected: sve2[1] equals `scalar`
   - Expected: sve[0] equals `aarch64_neon`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("collapses SVE and SVE2 hosts through neon before scalar")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val sve2 = _implemented_fallback_tiers("aarch64_sve2")
val sve = _implemented_fallback_tiers("aarch64_sve")
expect(sve2.len()).to_equal(2)  # oracle: sve2.len() must equal 2 — authoritative contract constant
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Host CPU runtime variants, REQ-001 through REQ-006: strongest executable black-box coverage currently reachable from SPipe, REQ-007 through REQ-013: contract-model coverage for still-unobservable internals.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-006:`
- `REQ-001`
- `REQ-006`
- `REQ-007`
- `REQ-013`
- `REQ-013:`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d141782a3e34e840c0fa57871b6d3d39a67859f347f822193184a1bc82fbe1e2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d141782a3e34e840c0fa57871b6d3d39a67859f347f822193184a1bc82fbe1e2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d141782a3e34e840c0fa57871b6d3d39a67859f347f822193184a1bc82fbe1e2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/03_system/app/compiler/feature/host_cpu_runtime_variants_spec.spl
mirror: doc/06_spec/03_system/app/compiler/feature/host_cpu_runtime_variants_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/compiler/feature/host_cpu_runtime_variants_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/compiler/feature/host_cpu_runtime_variants_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
