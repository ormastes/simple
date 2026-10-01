# reexport_physical_cache_spec

> Purpose: Prove that physical re-export cache.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# reexport_physical_cache_spec

Purpose: Prove that physical re-export cache.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/hir/reexport_physical_cache_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that physical re-export cache.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### physical re-export cache

#### allocates a unique nonzero generation for every successful freeze

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- allocates a unique nonzero generation for every successful freeze
- Verify: allocates a unique nonzero generation for every successful freeze
   - Expected: first.generation equals `first.surfaces[0].generation`
   - Expected: first.generation == second.generation is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allocates a unique nonzero generation for every successful freeze")
step("Verify: allocates a unique nonzero generation for every successful freeze")
# @req: REQ-COMPILER-HIR-001
val first = reexport_registry(false, false)
val second = reexport_registry(false, false)
expect(first.generation).to_be_greater_than(0)
expect(second.generation).to_be_greater_than(0)
expect(first.generation).to_equal(first.surfaces[0].generation)
expect(first.generation == second.generation).to_equal(false)
```

</details>

#### shares a positive result across aliases without another walk

- shares a positive result across aliases without another walk
- Verify: shares a positive result across aliases without another walk
   - Expected: first.found is true
   - Expected: first.module_index equals `1`
   - Expected: second.found is true
   - Expected: second.module_index equals `1`
   - Expected: lowering.reexport_chase_calls equals `calls_after_first`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shares a positive result across aliases without another walk")
step("Verify: shares a positive result across aliases without another walk")
val registry = reexport_registry(true, false)
var lowering = hirlowering_for_module("consumer", registry)
val first = lowering.find_reexport_source(0, "Hit")
val calls_after_first = lowering.reexport_chase_calls
val second = lowering.find_reexport_source(0, "Hit")
expect(first.found).to_equal(true)
expect(first.module_index).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(second.found).to_equal(true)
expect(second.module_index).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(lowering.reexport_chase_calls).to_equal(calls_after_first)
```

</details>

#### keeps preferred terminal aliases invariant under alias order

- keeps preferred terminal aliases invariant under alias order
- Verify: keeps preferred terminal aliases invariant under alias order
   - Expected: first.module_name equals `reversed.module_name`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps preferred terminal aliases invariant under alias order")
step("Verify: keeps preferred terminal aliases invariant under alias order")
val first_registry = reexport_registry(true, false)
val reversed_registry = reexport_registry(true, true)
var first_lowering = hirlowering_for_module("consumer", first_registry)
var reversed_lowering = hirlowering_for_module("consumer", reversed_registry)
val first = first_lowering.find_reexport_source(0, "Hit")
val reversed = reversed_lowering.find_reexport_source(0, "Hit")
expect(first.module_name).to_equal(reversed.module_name)
expect(first_registry.surfaces[1].preferred_registry_name).to_equal(
    reversed_registry.surfaces[1].preferred_registry_name)
```

</details>

#### restores first-src logical path behavior

- restores first-src logical path behavior
- Verify: restores first-src logical path behavior
   - Expected: registry.surfaces[0].logical_name equals `outer.src.inner`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("restores first-src logical path behavior")
step("Verify: restores first-src logical path behavior")
var surface = ModuleSurface.empty("repo/src/outer/src/inner.spl")
val registry = freeze_registry(
    [surface], {"outer.src.inner": 0}, ["outer.src.inner"], [0])
expect(registry.surfaces[0].logical_name).to_equal("outer.src.inner")
```

</details>

#### resolves relative routes from the physical path identity

- resolves relative routes from the physical path identity
- Verify: resolves relative routes from the physical path identity
   - Expected: registry.surfaces[0].logical_name equals `relative.facade`
   - Expected: registry.surfaces[0].import_target_indices equals `[1]`
   - Expected: result.found is true
   - Expected: result.module_index equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves relative routes from the physical path identity")
step("Verify: resolves relative routes from the physical path identity")
val registry = relative_registry()
var lowering = hirlowering_for_module("consumer", registry)
val result = lowering.find_reexport_source(0, "Relative")
expect(registry.surfaces[0].logical_name).to_equal("relative.facade")
expect(registry.surfaces[0].import_target_indices).to_equal([1])
expect(result.found).to_equal(true)
expect(result.module_index).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### keeps literal std precedence when lib has a conflicting surface

- keeps literal std precedence when lib has a conflicting surface
- Verify: keeps literal std precedence when lib has a conflicting surface
   - Expected: registry.surfaces[0].import_target_indices equals `[1]`
   - Expected: result.found is true
   - Expected: result.module_index equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps literal std precedence when lib has a conflicting surface")
step("Verify: keeps literal std precedence when lib has a conflicting surface")
val registry = std_lib_conflict_registry()
var lowering = hirlowering_for_module("consumer", registry)
val result = lowering.find_reexport_source(0, "Conflict")
expect(registry.surfaces[0].import_target_indices).to_equal([1])
expect(result.found).to_equal(true)
expect(result.module_index).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### invalidates a root cache for a declaration-only replacement

- invalidates a root cache for a declaration-only replacement
- Verify: invalidates a root cache for a declaration-only replacement
   - Expected: miss.found is false
   - Expected: hit.found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("invalidates a root cache for a declaration-only replacement")
step("Verify: invalidates a root cache for a declaration-only replacement")
val missing = declared_registry(false)
var lowering = hirlowering_for_module("consumer", missing)
val miss = lowering.find_reexport_source(0, "Real")
val declared = declared_registry(true)
lowering.module_surfaces = declared
val hit = lowering.find_reexport_source(0, "Real")
expect(miss.found).to_equal(false)
expect(hit.found).to_equal(true)
```

</details>

#### preserves warmed hit and miss roots across begin_module

- preserves warmed hit and miss roots across begin_module
- Verify: preserves warmed hit and miss roots across begin_module
   - Expected: hit_before.found is true
   - Expected: miss_before.found is false
   - Expected: hit_after.found is true
   - Expected: hit_after.module_index equals `1`
   - Expected: miss_after.found is false
   - Expected: lowering.reexport_chase_calls equals `calls_after_warm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves warmed hit and miss roots across begin_module")
step("Verify: preserves warmed hit and miss roots across begin_module")
val registry = reexport_registry(true, false)
var lowering = hirlowering_for_module("first", registry)
val hit_before = lowering.find_reexport_source(0, "Hit")
val miss_before = lowering.find_reexport_source(0, "Missing")
val calls_after_warm = lowering.reexport_chase_calls
lowering.begin_module("second")
val hit_after = lowering.find_reexport_source(0, "Hit")
val miss_after = lowering.find_reexport_source(0, "Missing")
expect(hit_before.found).to_equal(true)
expect(miss_before.found).to_equal(false)
expect(hit_after.found).to_equal(true)
expect(hit_after.module_index).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(miss_after.found).to_equal(false)
expect(lowering.reexport_chase_calls).to_equal(calls_after_warm)
```

</details>

#### finds a real declaration behind a re-export

- finds a real declaration behind a re-export
- Verify: finds a real declaration behind a re-export
   - Expected: result.found is true
   - Expected: result.module_index equals `1`
   - Expected: result.item_name equals `Real`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds a real declaration behind a re-export")
step("Verify: finds a real declaration behind a re-export")
val registry = declared_registry(true)
var lowering = hirlowering_for_module("consumer", registry)
val result = lowering.find_reexport_source(0, "Real")
expect(result.found).to_equal(true)
expect(result.module_index).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(result.item_name).to_equal("Real")
```

</details>

#### finds a hit behind a cycle

- finds a hit behind a cycle
- Verify: finds a hit behind a cycle
   - Expected: result.found is true
   - Expected: result.module_index equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds a hit behind a cycle")
step("Verify: finds a hit behind a cycle")
val registry = cyclic_registry(true)
var lowering = hirlowering_for_module("consumer", registry)
val result = lowering.find_reexport_source(0, "CycleHit")
expect(result.found).to_equal(true)
expect(result.module_index).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### rejects supported mutations after freeze

- rejects supported mutations after freeze
- Verify: rejects supported mutations after freeze
   - Expected: finished.is_ok() is true
   - Expected: builder_mutation.is_err() is true
   - Expected: registry_mutation.is_err() is true
   - Expected: origin_mutation.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects supported mutations after freeze")
step("Verify: rejects supported mutations after freeze")
var builder = ModuleSurfaceBuilder.new()
builder.surfaces = [ModuleSurface.empty("builder.surface")]
builder.add_indexed_name("builder.surface", 0)
val finished = builder.finish()
expect(finished.is_ok()).to_equal(true)
val builder_mutation = builder.add_indexed_name("late", 0)
expect(builder_mutation.is_err()).to_equal(true)
val registry = reexport_registry(true, false)
val registry_mutation = module_surfaces_freeze(registry)
expect(registry_mutation.is_err()).to_equal(true)
val origin_mutation = module_surface_export_origin_index_put(
    registry.surfaces[1].export_origin_index, "Late", "pkg.leaf", "Late", "explicit")
expect(origin_mutation.is_err()).to_equal(true)
```

</details>

#### rejects a facade index outside the current registry

- rejects a facade index outside the current registry
- Verify: rejects a facade index outside the current registry
   - Expected: result.found is false
   - Expected: lowering.reexport_root_memo_index.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a facade index outside the current registry")
step("Verify: rejects a facade index outside the current registry")
val current = reexport_registry(true, false)
var lowering = hirlowering_for_module("consumer", current)
val result = lowering.find_reexport_source(current.surfaces.len(), "Hit")
expect(result.found).to_equal(false)
expect(lowering.reexport_root_memo_index.len()).to_equal(0)
```

</details>

#### fails closed for invalid alignment and terminal owners

- fails closed for invalid alignment and terminal owners
- Verify: fails closed for invalid alignment and terminal owners
   - Expected: misaligned.found is false
   - Expected: bad_result.found is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed for invalid alignment and terminal owners")
step("Verify: fails closed for invalid alignment and terminal owners")
var surface = ModuleSurface.empty("broken")
surface.physical_index = 0
surface.generation = 1
surface.frozen = true
surface.preferred_registry_name = "broken"
surface.imports = [reexport_import("missing")]
surface.import_item_offsets = [0, 0]
surface.export_origin_index.frozen = true
var malformed = ModuleSurfacesByName(
    surfaces: [surface], index_by_name: {"broken": 0},
    ordered_names: ["broken"], ordered_indices: [0], generation: 1, frozen: true)
var lowering = hirlowering_for_module("consumer", malformed)
val misaligned = lowering.find_reexport_source(0, "Missing")
expect(misaligned.found).to_equal(false)
val bad_registry = unresolved_owner_registry()
var bad_lowering = hirlowering_for_module("consumer", bad_registry)
val bad_result = bad_lowering.find_reexport_source(0, "Bad")
expect(bad_result.found).to_equal(false)
```

</details>

#### does not cache a depth-truncated miss as a root result

- does not cache a depth-truncated miss as a root result
- Verify: does not cache a depth-truncated miss as a root result
   - Expected: first.found is false
   - Expected: second.found is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not cache a depth-truncated miss as a root result")
step("Verify: does not cache a depth-truncated miss as a root result")
val registry = depth_registry()
var lowering = hirlowering_for_module("consumer", registry)
val first = lowering.find_reexport_source(0, "Missing")
val calls_after_first = lowering.reexport_chase_calls
val second = lowering.find_reexport_source(0, "Missing")
expect(first.found).to_equal(false)
expect(second.found).to_equal(false)
expect(lowering.reexport_chase_calls).to_be_greater_than(calls_after_first)
```

</details>

#### keeps warmed generation checks allocation free

- keeps warmed generation checks allocation free
- Verify: keeps warmed generation checks allocation free
   - Expected: lowering.module_surfaces.generation equals `generation`
   - Expected: rt_heap_array_capacity_bytes() equals `before_capacity`
   - Expected: rt_heap_aux_live_bytes() equals `before_aux`
   - Expected: rt_heap_registry_count() equals `before_registry`
   - Expected: rt_heap_live_bytes() equals `before_live`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps warmed generation checks allocation free")
step("Verify: keeps warmed generation checks allocation free")
val registry = reexport_registry(true, false)
var lowering = hirlowering_for_module("consumer", registry)
val generation = registry.generation
lowering.find_reexport_source(0, "Hit")
val before_capacity = rt_heap_array_capacity_bytes()
val before_aux = rt_heap_aux_live_bytes()
val before_registry = rt_heap_registry_count()
val before_live = rt_heap_live_bytes()
var iteration = 0
while iteration < 1000:
    expect(lowering.module_surfaces.generation).to_equal(generation)
    lowering.find_reexport_source(0, "Hit")
    iteration = iteration + 1
expect(rt_heap_array_capacity_bytes()).to_equal(before_capacity)
expect(rt_heap_aux_live_bytes()).to_equal(before_aux)
expect(rt_heap_registry_count()).to_equal(before_registry)
expect(rt_heap_live_bytes()).to_equal(before_live)
```

</details>

#### keeps one memo row per (physical facade, wanted) and probes it in O(1)

- keeps one memo row per (physical facade, wanted) and probes it in O(1)
- Verify: keeps one memo row per (physical facade, wanted) and probes it in O(1)
   - Expected: result.found is false
   - Expected: lowering.reexport_root_memo_index.len() equals `600`
   - Expected: lowering.reexport_root_memo_item.len() equals `600`
   - Expected: lowering.reexport_root_memo_index["0 Missing.7"] equals `-1`
   - Expected: lowering.reexport_chase_memo_hits equals `hits_before + 2`
   - Expected: lowering.reexport_root_memo_index["0 Hit"] equals `1`
   - Expected: lowering.reexport_root_memo_item["0 Hit"] equals `Hit`
   - Expected: lowering.reexport_root_memo_index.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps one memo row per (physical facade, wanted) and probes it in O(1)")
step("Verify: keeps one memo row per (physical facade, wanted) and probes it in O(1)")
# REXMEMO (2026-08-21). d757f7d70d0 deleted the root memo outright, so
# every `find_reexport_source` re-walked the facade's reachable import
# graph: a MISS visits all of it, once per name, per importer. On the
# 662-module closure `glob` went 69 s -> 195 s for the SAME 73 roots.
# The memo is a Dict keyed by PHYSICAL index + wanted (aliases share a
# row, no 512 cap, no linear scan), dropped only on a generation change.
# Counter, not wall clock: the hit count cannot move on the pre-fix code.
val registry = reexport_registry(true, false)
var lowering = hirlowering_for_module("consumer", registry)
var index = 0
while index < 600:
    val result = lowering.find_reexport_source(0, "Missing.{index}")
    expect(result.found).to_equal(false)
    index = index + 1
expect(lowering.reexport_root_memo_index.len()).to_equal(600)
expect(lowering.reexport_root_memo_item.len()).to_equal(600)
expect(lowering.reexport_root_memo_index["0 Missing.7"]).to_equal(-1)
val hits_before = lowering.reexport_chase_memo_hits
val calls_before = lowering.reexport_chase_calls
lowering.find_reexport_source(0, "Missing.7")
lowering.find_reexport_source(0, "Hit")
lowering.find_reexport_source(0, "Hit")
expect(lowering.reexport_chase_memo_hits).to_equal(hits_before + 2)
expect(lowering.reexport_chase_calls).to_be_greater_than(calls_before)
expect(lowering.reexport_root_memo_index["0 Hit"]).to_equal(1)
expect(lowering.reexport_root_memo_item["0 Hit"]).to_equal("Hit")
# A new frozen registry (new generation) must drop every row.
lowering.module_surfaces = reexport_registry(true, false)
lowering.find_reexport_source(0, "Hit")
expect(lowering.reexport_root_memo_index.len()).to_equal(1)
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

- `REQ-SSPEC-UNIT`
- `REQ-COMPILER-HIR-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8c63f3feeb33a4ca369dd22e99defe89fd1a03a03a16ec16675335a53caab0ab`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8c63f3feeb33a4ca369dd22e99defe89fd1a03a03a16ec16675335a53caab0ab`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8c63f3feeb33a4ca369dd22e99defe89fd1a03a03a16ec16675335a53caab0ab`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler/hir/reexport_physical_cache_spec.spl
mirror: doc/06_spec/unit/compiler/hir/reexport_physical_cache_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/hir/reexport_physical_cache_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/hir/reexport_physical_cache_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/hir/reexport_physical_cache_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/hir/reexport_physical_cache_spec.spl:175:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allocates a unique nonzero generation for every successful freeze' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/hir/reexport_physical_cache_spec.spl:187:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shares a positive result across aliases without another walk' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/hir/reexport_physical_cache_spec.spl:202:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps preferred terminal aliases invariant under alias order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
