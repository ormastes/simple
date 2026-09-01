# Gc Runtime Contract Specification

> Tests covering nogc_sync_mut GC and reference contracts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gc Runtime Contract Specification

## Scenarios

### nogc_sync_mut GC and reference contracts

#### exports usable GC configuration and metadata types

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- exports usable GC configuration and metadata types
   - Expected: default_config.young_size equals `1024 * 1024`
   - Expected: default_config.old_size equals `4 * 1024 * 1024`
   - Expected: default_config.incremental is false
   - Expected: sized_config.young_size equals `2 * 1024`
   - Expected: sized_config.old_size equals `8 * 1024`
   - Expected: header.size equals `64`
   - Expected: header.type_id equals `7`
   - Expected: header.color equals `GcColor.White`
   - Expected: header.marked is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("exports usable GC configuration and metadata types")
val default_config = GcConfig.default()
expect(default_config.young_size).to_equal(1024 * 1024)
expect(default_config.old_size).to_equal(4 * 1024 * 1024)
expect(default_config.incremental).to_equal(false)

val sized_config = GcConfig.with_heap_size(10 * 1024)
expect(sized_config.young_size).to_equal(2 * 1024)
expect(sized_config.old_size).to_equal(8 * 1024)

val header = GcObjectHeader.new(64, 7)
expect(header.size).to_equal(64)
expect(header.type_id).to_equal(7)
expect(header.color).to_equal(GcColor.White)
expect(header.marked).to_equal(false)
```

</details>

#### tracks empty GC stats deterministically

- tracks empty GC stats deterministically
   - Expected: stats.collections equals `0`
   - Expected: stats.objects_allocated equals `0`
   - Expected: stats.avg_pause_time() equals `0`
   - Expected: stats.survival_rate() equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("tracks empty GC stats deterministically")
val stats = GcStats.new()
expect(stats.collections).to_equal(0)
expect(stats.objects_allocated).to_equal(0)
expect(stats.avg_pause_time()).to_equal(0)
expect(stats.survival_rate()).to_equal(0.0)
```

</details>

#### exports pointer ownership helpers from the no-GC backend

- exports pointer ownership helpers from the no-GC backend
   - Expected: unique_get(unique) equals `-1`
   - Expected: unique_get(moved) equals `41`
   - Expected: weak_upgrade(weak) equals `77`
   - Expected: weak_upgrade(weak) equals `-1`
   - Expected: handle_deref(handle) equals `13`
   - Expected: handle_free(handle) is true
   - Expected: handle_deref(handle) equals `-1`
   - Expected: state.valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("exports pointer ownership helpers from the no-GC backend")
unique_reset()
val unique = unique_new(41, "gc-contract")
val moved = unique_move(unique)
expect(unique_get(unique)).to_equal(-1)
expect(unique_get(moved)).to_equal(41)

weak_reset()
val weak_id = weak_register(77)
val weak = weak_create(weak_id)
expect(weak_upgrade(weak)).to_equal(77)
weak_invalidate(weak_id)
expect(weak_upgrade(weak)).to_equal(-1)

handle_pool_new(4)
val handle = handle_alloc(13)
expect(handle_deref(handle)).to_equal(13)
expect(handle_free(handle)).to_equal(true)
expect(handle_deref(handle)).to_equal(-1)

val state = ptr_state_valid()
expect(state.valid).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/gc_runtime_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nogc_sync_mut GC and reference contracts.
- nogc_sync_mut GC and reference contracts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bd44231e34d391270e617554aa45120192a1cb1dd2e8d6f373dbab1b24c3319b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bd44231e34d391270e617554aa45120192a1cb1dd2e8d6f373dbab1b24c3319b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bd44231e34d391270e617554aa45120192a1cb1dd2e8d6f373dbab1b24c3319b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/nogc_sync_mut/gc_runtime_contract_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/gc_runtime_contract_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/gc_runtime_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/gc_runtime_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/gc_runtime_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/gc_runtime_contract_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exports usable GC configuration and metadata types' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/gc_runtime_contract_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tracks empty GC stats deterministically' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/gc_runtime_contract_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exports pointer ownership helpers from the no-GC backend' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
