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


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-001
# @req REQ-006
# @req REQ-007
# @req REQ-013
# @req REQ-SSPEC-SYSTEM
step("passes the targeted simple-simd host-config regression suite")
val target_dir = _tmp_target_dir("simd")
val command = "cd '{_repo_root()}' && CARGO_TARGET_DIR='{target_dir}' CARGO_NET_OFFLINE=true cargo test -p simple-simd --lib --offline"
val result = _run_shell(command)

val combined = result.stdout + "\n" + result.stderr
assert_equal(result.exit_code, 0)
assert_equal(combined.contains("writes_and_reads_cpu_config_round_trip"), true)
assert_equal(combined.contains("clamps_invalid_enabled_values_and_rewrites_file"), true)
assert_equal(combined.contains("cpu_config_path_honors_trimmed_override"), true)
assert_equal(combined.contains("active_simd_tier_prefers_env_override_over_config"), true)
assert_equal(combined.contains("host_cpu_config_reloads_after_on_disk_edit_in_same_process"), true)
assert_equal(combined.contains("canonical_rewrite_uses_simple_supported_intersection"), true)
```

</details>

#### models invalid override fallback when no direct Simple hook can observe it

- models invalid override fallback when no direct Simple hook can observe it


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("models invalid override fallback when no direct Simple hook can observe it")
assert_equal(_active_tier_model("definitely-not-a-tier", "scalar", "x86_64_avx2"), "scalar")
```

</details>

### REQ-007 through REQ-013: contract-model coverage for still-unobservable internals

#### keeps only support intersect simple_support in canonical order

- keeps only support intersect simple_support in canonical order


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps only support intersect simple_support in canonical order")
val clamped = _clamp_instruction_sets(
    ["sse2", "avx2", "avx512f"],
    ["sse2", "avx2"],
    ["avx2", "sse2", "avx512f"]
)
assert_equal(clamped.len(), 2)
assert_equal(clamped[0], "sse2")
assert_equal(clamped[1], "avx2")
```

</details>

#### probes compatible sibling runtime variants before the scalar fallback

- probes compatible sibling runtime variants before the scalar fallback


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("probes compatible sibling runtime variants before the scalar fallback")
val candidates = _runtime_library_candidates("", "x86_64_avx512")
assert_equal(candidates.len(), 3)
assert_equal(candidates[0], "libsimple_runtime.x86_64_avx2.so")
assert_equal(candidates[1], "libsimple_runtime.x86_64_sse2.so")
assert_equal(candidates[2], "libsimple_runtime.so")
```

</details>

#### keeps explicit-path probes in the sibling directory

- keeps explicit-path probes in the sibling directory


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps explicit-path probes in the sibling directory")
val candidates = _runtime_library_candidates("/tmp/runtime", "aarch64_sve2")
assert_equal(candidates.len(), 2)
assert_equal(candidates[0], "/tmp/runtime/libsimple_runtime.aarch64_neon.so")
assert_equal(candidates[1], "/tmp/runtime/libsimple_runtime.so")
```

</details>

#### falls through lower compatible embedded variants until a present resource is found

- falls through lower compatible embedded variants until a present resource is found


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("falls through lower compatible embedded variants until a present resource is found")
val selected = _select_embedded_runtime_resource(
    "x86_64_avx512",
    ["x86_64_avx2", "x86_64_sse2", "scalar"],
    ["runtime/avx2.so", "runtime/sse2.so", "runtime/scalar.so"],
    ["runtime/sse2.so", "runtime/scalar.so"]
)
assert_equal(selected, "runtime/sse2.so")
```

</details>

#### fails closed when manifest metadata is truncated or malformed

- fails closed when manifest metadata is truncated or malformed


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fails closed when manifest metadata is truncated or malformed")
assert_equal(_manifest_is_valid(true, false, true), false)
assert_equal(_manifest_is_valid(true, true, false), false)
assert_equal(_manifest_is_valid(false, false, false), true)
```

</details>

#### changes cache identity when the active tier changes

- changes cache identity when the active tier changes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("changes cache identity when the active tier changes")
val scalar_key = _cache_identity("object:main", "scalar")
val sse2_key = _cache_identity("object:main", "x86_64_sse2")
expect(scalar_key).to_not_equal(sse2_key)
```

</details>

#### changes stdlib root ordering when the configured tier changes

- changes stdlib root ordering when the configured tier changes


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("changes stdlib root ordering when the configured tier changes")
val scalar_roots = _stdlib_root_candidates("src/lib/std/src", "scalar")
val sse2_roots = _stdlib_root_candidates("src/lib/std/src", "x86_64_sse2")
assert_equal(scalar_roots.len(), 1)
assert_equal(scalar_roots[0], "src/lib/std/src")
assert_equal(sse2_roots.len(), 2)
assert_equal(sse2_roots[0], "src/lib/std/variants/x86_64_sse2/src")
assert_equal(sse2_roots[1], "src/lib/std/src")
```

</details>

#### collapses higher x86 tiers to implemented v1 runtime artifacts

- collapses higher x86 tiers to implemented v1 runtime artifacts


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("collapses higher x86 tiers to implemented v1 runtime artifacts")
val x86 = _implemented_fallback_tiers("x86_64_avx512")
assert_equal(x86.len(), 3)
assert_equal(x86[0], "x86_64_avx2")
assert_equal(x86[1], "x86_64_sse2")
assert_equal(x86[2], "scalar")
```

</details>

#### collapses SVE and SVE2 hosts through neon before scalar

- collapses SVE and SVE2 hosts through neon before scalar


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("collapses SVE and SVE2 hosts through neon before scalar")
val sve2 = _implemented_fallback_tiers("aarch64_sve2")
val sve = _implemented_fallback_tiers("aarch64_sve")
assert_equal(sve2.len(), 2)
assert_equal(sve2[0], "aarch64_neon")
assert_equal(sve2[1], "scalar")
assert_equal(sve[0], "aarch64_neon")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/system/app/compiler/feature/host_cpu_runtime_variants_spec.spl` |
| Updated | 2026-08-27 |
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

- Canonical SPipe generation for source `3caf62c8e60c7e0afa48cae22ca78b420f2ff275ef43c1da5c17cfc51dbff79f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3caf62c8e60c7e0afa48cae22ca78b420f2ff275ef43c1da5c17cfc51dbff79f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3caf62c8e60c7e0afa48cae22ca78b420f2ff275ef43c1da5c17cfc51dbff79f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/system/app/compiler/feature/host_cpu_runtime_variants_spec.spl
mirror: doc/06_spec/system/app/compiler/feature/host_cpu_runtime_variants_spec.md (current)
findings: 6 blockers: 0
  narrative=80 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/system/app/compiler/feature/host_cpu_runtime_variants_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/system/app/compiler/feature/host_cpu_runtime_variants_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/system/app/compiler/feature/host_cpu_runtime_variants_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/system/app/compiler/feature/host_cpu_runtime_variants_spec.spl:155:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes the targeted simple-simd host-config regression suite' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/system/app/compiler/feature/host_cpu_runtime_variants_spec.spl:175:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'models invalid override fallback when no direct Simple hook can observe it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/system/app/compiler/feature/host_cpu_runtime_variants_spec.spl:181:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps only support intersect simple_support in canonical order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
