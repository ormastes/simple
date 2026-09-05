# resource_lifecycle_spec

> Purpose: Prove that ResourceLifecycleManager.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# resource_lifecycle_spec

Purpose: Prove that ResourceLifecycleManager.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/loader/resource_lifecycle_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that ResourceLifecycleManager.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### ResourceLifecycleManager

### module tracking

#### tracks a new module after on_module_load

- tracks a new module after on_module_load
- Verify: tracks a new module after on_module_load
   - Expected: lm_is_tracked("/test/mod_a.smf") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("tracks a new module after on_module_load")
step("Verify: tracks a new module after on_module_load")
# @req: REQ-COMPILER-LOADER-001
lm_reset()
lm_on_module_load("/test/mod_a.smf")
expect(lm_is_tracked("/test/mod_a.smf")).to_equal(true)
```

</details>

#### reports false for untracked module

- reports false for untracked module
- Verify: reports false for untracked module
   - Expected: lm_is_tracked("/nonexistent") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports false for untracked module")
step("Verify: reports false for untracked module")
lm_reset()
expect(lm_is_tracked("/nonexistent")).to_equal(false)
```

</details>

#### counts multiple tracked modules

- counts multiple tracked modules
- Verify: counts multiple tracked modules
   - Expected: lm_tracked_module_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("counts multiple tracked modules")
step("Verify: counts multiple tracked modules")
lm_reset()
lm_on_module_load("/a.smf")
lm_on_module_load("/b.smf")
expect(lm_tracked_module_count()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

### symbol and JIT tracking

#### records symbols mapped for a module

- records symbols mapped for a module
- Verify: records symbols mapped for a module
   - Expected: lm_get_symbols_for("/mod.smf") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("records symbols mapped for a module")
step("Verify: records symbols mapped for a module")
lm_reset()
lm_on_module_load("/mod.smf")
lm_on_symbol_mapped("/mod.smf", "func_a")
lm_on_symbol_mapped("/mod.smf", "func_b")
expect(lm_get_symbols_for("/mod.smf")).to_equal(2)
```

</details>

#### records JIT symbol origin for unload

- records JIT symbol origin for unload
- Verify: records JIT symbol origin for unload
   - Expected: lm_tracked_jit_count() equals `1`
   - Expected: origin equals `/mod.smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("records JIT symbol origin for unload")
step("Verify: records JIT symbol origin for unload")
lm_reset()
lm_on_module_load("/mod.smf")
lm_on_jit_triggered("/mod.smf", "Vec$i64_push")
expect(lm_tracked_jit_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
val origin = lm_get_jit_origin("Vec$i64_push")
expect(origin).to_equal("/mod.smf")
```

</details>

#### returns empty for unknown JIT symbol

- returns empty for unknown JIT symbol
- Verify: returns empty for unknown JIT symbol
   - Expected: origin equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns empty for unknown JIT symbol")
step("Verify: returns empty for unknown JIT symbol")
lm_reset()
val origin = lm_get_jit_origin("nonexistent")
expect(origin).to_equal("")
```

</details>

### metadata and SMF tracking

#### records metadata path for module

- records metadata path for module
- Verify: records metadata path for module
   - Expected: lm_is_tracked("/mod.smf") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("records metadata path for module")
step("Verify: records metadata path for module")
lm_reset()
lm_on_module_load("/mod.smf")
lm_on_metadata_loaded("/mod.smf", "/mod.smf")
expect(lm_is_tracked("/mod.smf")).to_equal(true)
```

</details>

#### tracks SMF cache access

- tracks SMF cache access
- Verify: tracks SMF cache access
   - Expected: smf_get_ref_count("/shared.smf") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("tracks SMF cache access")
step("Verify: tracks SMF cache access")
lm_reset()
smf_reset()
lm_on_module_load("/mod.smf")
lm_on_smf_accessed("/mod.smf", "/shared.smf")
smf_inc("/shared.smf")
expect(smf_get_ref_count("/shared.smf")).to_equal(1)
```

</details>

### SmfCacheManager

### ref counting

#### starts at zero ref count

- starts at zero ref count
- Verify: starts at zero ref count
   - Expected: smf_get_ref_count("/test.smf") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("starts at zero ref count")
step("Verify: starts at zero ref count")
smf_reset()
expect(smf_get_ref_count("/test.smf")).to_equal(0)
```

</details>

#### increments ref count

- increments ref count
- Verify: increments ref count
   - Expected: smf_get_ref_count("/test.smf") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("increments ref count")
step("Verify: increments ref count")
smf_reset()
smf_inc("/test.smf")
expect(smf_get_ref_count("/test.smf")).to_equal(1)
```

</details>

#### increments multiple times

- increments multiple times
- Verify: increments multiple times
   - Expected: smf_get_ref_count("/test.smf") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("increments multiple times")
step("Verify: increments multiple times")
smf_reset()
smf_inc("/test.smf")
smf_inc("/test.smf")
smf_inc("/test.smf")
expect(smf_get_ref_count("/test.smf")).to_equal(3)
```

</details>

#### decrements ref count

- decrements ref count
- Verify: decrements ref count
   - Expected: smf_get_ref_count("/test.smf") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("decrements ref count")
step("Verify: decrements ref count")
smf_reset()
smf_inc("/test.smf")
smf_inc("/test.smf")
smf_dec("/test.smf")
expect(smf_get_ref_count("/test.smf")).to_equal(1)
```

</details>

#### evicts when ref count reaches zero

- evicts when ref count reaches zero
- Verify: evicts when ref count reaches zero
   - Expected: smf_tracked_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("evicts when ref count reaches zero")
step("Verify: evicts when ref count reaches zero")
smf_reset()
smf_inc("/test.smf")
smf_dec("/test.smf")
expect(smf_tracked_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### multi-path tracking

#### tracks independent paths

- tracks independent paths
- Verify: tracks independent paths
   - Expected: smf_tracked_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("tracks independent paths")
step("Verify: tracks independent paths")
smf_reset()
smf_inc("/a.smf")
smf_inc("/b.smf")
expect(smf_tracked_count()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### force clear resets all

- force clear resets all
- Verify: force clear resets all
   - Expected: smf_tracked_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("force clear resets all")
step("Verify: force clear resets all")
smf_reset()
smf_inc("/a.smf")
smf_inc("/b.smf")
smf_force_clear()
expect(smf_tracked_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### ignores dec on untracked path

- ignores dec on untracked path
- Verify: ignores dec on untracked path
   - Expected: smf_tracked_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("ignores dec on untracked path")
step("Verify: ignores dec on untracked path")
smf_reset()
smf_dec("/nonexistent.smf")
expect(smf_tracked_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMPILER-LOADER-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f528ec6abf3d21a708108949a1d0d55d97985b5a3fece6fc1e52fe676771b108`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f528ec6abf3d21a708108949a1d0d55d97985b5a3fece6fc1e52fe676771b108`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f528ec6abf3d21a708108949a1d0d55d97985b5a3fece6fc1e52fe676771b108`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/loader/resource_lifecycle_spec.spl
mirror: doc/06_spec/01_unit/compiler/loader/resource_lifecycle_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/loader/resource_lifecycle_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/loader/resource_lifecycle_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/loader/resource_lifecycle_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/loader/resource_lifecycle_spec.spl:214:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tracks a new module after on_module_load' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/loader/resource_lifecycle_spec.spl:223:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports false for untracked module' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/loader/resource_lifecycle_spec.spl:230:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'counts multiple tracked modules' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
