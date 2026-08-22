# host_cpu_runtime_variants_spec

> Verifies the host cpu runtime variants behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# host_cpu_runtime_variants_spec

Verifies the host cpu runtime variants behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/compiler/feature/host_cpu_runtime_variants_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the host cpu runtime variants behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Host CPU runtime variants

### REQ-001 through REQ-006: strongest executable black-box coverage currently reachable from SPipe

#### passes the targeted simple-simd host-config regression suite

- Verify: passes the targeted simple-simd host-config regression suite
   - Expected: result.exit_code equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: combined contains `writes_and_reads_cpu_config_round_trip`
   - Expected: combined contains `clamps_invalid_enabled_values_and_rewrites_file`
   - Expected: combined contains `cpu_config_path_honors_trimmed_override`
   - Expected: combined contains `active_simd_tier_prefers_env_override_over_config`
   - Expected: combined contains `host_cpu_config_reloads_after_on_disk_edit_in_same_process`
   - Expected: combined contains `canonical_rewrite_uses_simple_supported_intersection`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-006 REQ-007 REQ-013
step("Verify: passes the targeted simple-simd host-config regression suite")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val target_dir = _tmp_target_dir("simd")
val command = "cd '{_repo_root()}' && CARGO_TARGET_DIR='{target_dir}' CARGO_NET_OFFLINE=true cargo test -p simple-simd --lib --offline"
val result = _run_shell(command)

val combined = result.stdout + "\n" + result.stderr
expect(result.exit_code).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(combined.contains("writes_and_reads_cpu_config_round_trip")).to_equal(true)
expect(combined.contains("clamps_invalid_enabled_values_and_rewrites_file")).to_equal(true)
expect(combined.contains("cpu_config_path_honors_trimmed_override")).to_equal(true)
expect(combined.contains("active_simd_tier_prefers_env_override_over_config")).to_equal(true)
expect(combined.contains("host_cpu_config_reloads_after_on_disk_edit_in_same_process")).to_equal(true)
expect(combined.contains("canonical_rewrite_uses_simple_supported_intersection")).to_equal(true)
```

</details>

#### models invalid override fallback when no direct Simple hook can observe it

- Verify: models invalid override fallback when no direct Simple hook can observe it
   - Expected: _active_tier_model("definitely-not-a-tier", "scalar", "x86_64_avx2") equals `scalar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-006 REQ-007 REQ-013
step("Verify: models invalid override fallback when no direct Simple hook can observe it")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(_active_tier_model("definitely-not-a-tier", "scalar", "x86_64_avx2")).to_equal("scalar")
```

</details>

### REQ-007 through REQ-013: contract-model coverage for still-unobservable internals

#### keeps only support intersect simple_support in canonical order

- Verify: keeps only support intersect simple_support in canonical order
   - Expected: clamped.len() equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: clamped[0] equals `sse2`
   - Expected: clamped[1] equals `avx2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-006 REQ-007 REQ-013
step("Verify: keeps only support intersect simple_support in canonical order")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val clamped = _clamp_instruction_sets(
    ["sse2", "avx2", "avx512f"],
    ["sse2", "avx2"],
    ["avx2", "sse2", "avx512f"]
)
expect(clamped.len()).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(clamped[0]).to_equal("sse2")
expect(clamped[1]).to_equal("avx2")
```

</details>

#### probes compatible sibling runtime variants before the scalar fallback

- Verify: probes compatible sibling runtime variants before the scalar fallback
   - Expected: candidates.len() equals `3)  # oracle: pinned constant asserted by this scenario`
   - Expected: candidates[0] equals `libsimple_runtime.x86_64_avx2.so`
   - Expected: candidates[1] equals `libsimple_runtime.x86_64_sse2.so`
   - Expected: candidates[2] equals `libsimple_runtime.so`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-006 REQ-007 REQ-013
step("Verify: probes compatible sibling runtime variants before the scalar fallback")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val candidates = _runtime_library_candidates("", "x86_64_avx512")
expect(candidates.len()).to_equal(3)  # oracle: pinned constant asserted by this scenario
expect(candidates[0]).to_equal("libsimple_runtime.x86_64_avx2.so")
expect(candidates[1]).to_equal("libsimple_runtime.x86_64_sse2.so")
expect(candidates[2]).to_equal("libsimple_runtime.so")
```

</details>

#### keeps explicit-path probes in the sibling directory

- Verify: keeps explicit-path probes in the sibling directory
   - Expected: candidates.len() equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: candidates[0] equals `/tmp/runtime/libsimple_runtime.aarch64_neon.so`
   - Expected: candidates[1] equals `/tmp/runtime/libsimple_runtime.so`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-006 REQ-007 REQ-013
step("Verify: keeps explicit-path probes in the sibling directory")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val candidates = _runtime_library_candidates("/tmp/runtime", "aarch64_sve2")
expect(candidates.len()).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(candidates[0]).to_equal("/tmp/runtime/libsimple_runtime.aarch64_neon.so")
expect(candidates[1]).to_equal("/tmp/runtime/libsimple_runtime.so")
```

</details>

#### falls through lower compatible embedded variants until a present resource is found

- Verify: falls through lower compatible embedded variants until a present resource is found
   - Expected: selected equals `runtime/sse2.so`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-006 REQ-007 REQ-013
step("Verify: falls through lower compatible embedded variants until a present resource is found")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: fails closed when manifest metadata is truncated or malformed
   - Expected: _manifest_is_valid(true, false, true) is false
   - Expected: _manifest_is_valid(true, true, false) is false
   - Expected: _manifest_is_valid(false, false, false) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-006 REQ-007 REQ-013
step("Verify: fails closed when manifest metadata is truncated or malformed")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(_manifest_is_valid(true, false, true)).to_equal(false)
expect(_manifest_is_valid(true, true, false)).to_equal(false)
expect(_manifest_is_valid(false, false, false)).to_equal(true)
```

</details>

#### changes cache identity when the active tier changes

- Verify: changes cache identity when the active tier changes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-006 REQ-007 REQ-013
step("Verify: changes cache identity when the active tier changes")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val scalar_key = _cache_identity("object:main", "scalar")
val sse2_key = _cache_identity("object:main", "x86_64_sse2")
expect(scalar_key).to_not_equal(sse2_key)
```

</details>

#### changes stdlib root ordering when the configured tier changes

- Verify: changes stdlib root ordering when the configured tier changes
   - Expected: scalar_roots.len() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: scalar_roots[0] equals `src/lib/std/src`
   - Expected: sse2_roots.len() equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: sse2_roots[0] equals `src/lib/std/variants/x86_64_sse2/src`
   - Expected: sse2_roots[1] equals `src/lib/std/src`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-006 REQ-007 REQ-013
step("Verify: changes stdlib root ordering when the configured tier changes")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val scalar_roots = _stdlib_root_candidates("src/lib/std/src", "scalar")
val sse2_roots = _stdlib_root_candidates("src/lib/std/src", "x86_64_sse2")
expect(scalar_roots.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(scalar_roots[0]).to_equal("src/lib/std/src")
expect(sse2_roots.len()).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(sse2_roots[0]).to_equal("src/lib/std/variants/x86_64_sse2/src")
expect(sse2_roots[1]).to_equal("src/lib/std/src")
```

</details>

#### collapses higher x86 tiers to implemented v1 runtime artifacts

- Verify: collapses higher x86 tiers to implemented v1 runtime artifacts
   - Expected: x86.len() equals `3)  # oracle: pinned constant asserted by this scenario`
   - Expected: x86[0] equals `x86_64_avx2`
   - Expected: x86[1] equals `x86_64_sse2`
   - Expected: x86[2] equals `scalar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-006 REQ-007 REQ-013
step("Verify: collapses higher x86 tiers to implemented v1 runtime artifacts")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val x86 = _implemented_fallback_tiers("x86_64_avx512")
expect(x86.len()).to_equal(3)  # oracle: pinned constant asserted by this scenario
expect(x86[0]).to_equal("x86_64_avx2")
expect(x86[1]).to_equal("x86_64_sse2")
expect(x86[2]).to_equal("scalar")
```

</details>

#### collapses SVE and SVE2 hosts through neon before scalar

- Verify: collapses SVE and SVE2 hosts through neon before scalar
   - Expected: sve2.len() equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: sve2[0] equals `aarch64_neon`
   - Expected: sve2[1] equals `scalar`
   - Expected: sve[0] equals `aarch64_neon`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-006 REQ-007 REQ-013
step("Verify: collapses SVE and SVE2 hosts through neon before scalar")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val sve2 = _implemented_fallback_tiers("aarch64_sve2")
val sve = _implemented_fallback_tiers("aarch64_sve")
expect(sve2.len()).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(sve2[0]).to_equal("aarch64_neon")
expect(sve2[1]).to_equal("scalar")
expect(sve[0]).to_equal("aarch64_neon")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `57aa91e1708e7174ec172986d9841e47ebfe6296ea0f875d18afafc2d43f925b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `57aa91e1708e7174ec172986d9841e47ebfe6296ea0f875d18afafc2d43f925b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `57aa91e1708e7174ec172986d9841e47ebfe6296ea0f875d18afafc2d43f925b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/app/compiler/feature/host_cpu_runtime_variants_spec.spl
mirror: doc/06_spec/03_system/app/compiler/feature/host_cpu_runtime_variants_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/compiler/feature/host_cpu_runtime_variants_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/compiler/feature/host_cpu_runtime_variants_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/compiler/feature/host_cpu_runtime_variants_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
