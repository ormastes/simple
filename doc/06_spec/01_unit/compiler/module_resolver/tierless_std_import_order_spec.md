# Tierless Std Import Order Specification

> Tests covering tier_ordered_subdirs — reproducer, tier_ordered_subdirs — detection (must be a permutation).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tierless Std Import Order Specification

## Scenarios

### tier_ordered_subdirs — reproducer

#### puts common first regardless of the incoming listing order

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- puts common first regardless of the incoming listing order
   - Expected: tier_ordered_subdirs(listing)[0] equals `common`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("puts common first regardless of the incoming listing order")
val listing = ["gc_async_mut", "nogc_sync_mut", "common"]
expect(tier_ordered_subdirs(listing)[0]).to_equal("common")
```

</details>

#### yields the SAME order for two different readdir permutations

- yields the SAME order for two different readdir permutations
   - Expected: a equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("yields the SAME order for two different readdir permutations")
val a = tier_ordered_subdirs(["gc_async_mut", "common", "nogc_async_mut", "nogc_sync_mut"])
val b = tier_ordered_subdirs(["nogc_sync_mut", "nogc_async_mut", "common", "gc_async_mut"])
expect(a).to_equal(b)
```

</details>

#### prefers common over gc_async_mut for a path present in both

- prefers common over gc_async_mut for a path present in both
   - Expected: index_of(out, "common") < index_of(out, "gc_async_mut") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("prefers common over gc_async_mut for a path present in both")
val out = tier_ordered_subdirs(["gc_async_mut", "common"])
expect(index_of(out, "common") < index_of(out, "gc_async_mut")).to_equal(true)
```

</details>

#### prefers nogc_sync_mut over gc_async_mut

- prefers nogc_sync_mut over gc_async_mut
   - Expected: index_of(out, "nogc_sync_mut") < index_of(out, "gc_async_mut") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("prefers nogc_sync_mut over gc_async_mut")
val out = tier_ordered_subdirs(["gc_async_mut", "nogc_sync_mut"])
expect(index_of(out, "nogc_sync_mut") < index_of(out, "gc_async_mut")).to_equal(true)
```

</details>

### tier_ordered_subdirs — detection (must be a permutation)

#### drops nothing: output length equals input length

- drops nothing: output length equals input length
   - Expected: tier_ordered_subdirs(listing).len() equals `listing.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("drops nothing: output length equals input length")
val listing = ["gc_async_mut", "vendor", "common", "nogc_sync_mut", "scratch"]
expect(tier_ordered_subdirs(listing).len()).to_equal(listing.len())
```

</details>

#### keeps every non-tier entry rather than filtering it out

- keeps every non-tier entry rather than filtering it out
   - Expected: index_of(out, "vendor") >= 0 is true
   - Expected: index_of(out, "scratch") >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps every non-tier entry rather than filtering it out")
val out = tier_ordered_subdirs(["vendor", "common", "scratch"])
expect(index_of(out, "vendor") >= 0).to_equal(true)
expect(index_of(out, "scratch") >= 0).to_equal(true)
```

</details>

#### sorts every non-tier entry AFTER every canonical tier

- sorts every non-tier entry AFTER every canonical tier
   - Expected: index_of(out, "vendor") > index_of(out, "gc_async_mut") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("sorts every non-tier entry AFTER every canonical tier")
val out = tier_ordered_subdirs(["vendor", "gc_async_mut", "common"])
expect(index_of(out, "vendor") > index_of(out, "gc_async_mut")).to_equal(true)
```

</details>

#### preserves the relative order of non-tier entries

- preserves the relative order of non-tier entries
   - Expected: index_of(out, "zeta") < index_of(out, "alpha") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves the relative order of non-tier entries")
val out = tier_ordered_subdirs(["zeta", "common", "alpha"])
expect(index_of(out, "zeta") < index_of(out, "alpha")).to_equal(true)
```

</details>

#### is a no-op on a listing with no canonical tiers

- is a no-op on a listing with no canonical tiers
   - Expected: tier_ordered_subdirs(listing) equals `listing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("is a no-op on a listing with no canonical tiers")
val listing = ["vendor", "scratch"]
expect(tier_ordered_subdirs(listing)).to_equal(listing)
```

</details>

#### handles an empty listing

- handles an empty listing
   - Expected: tier_ordered_subdirs([]).len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("handles an empty listing")
expect(tier_ordered_subdirs([]).len()).to_equal(0)
```

</details>

#### orders a full five-tier listing exactly as TIER_PRECEDENCE declares

- orders a full five-tier listing exactly as TIER_PRECEDENCE declares
   - Expected: tier_ordered_subdirs(shuffled) equals `TIER_PRECEDENCE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("orders a full five-tier listing exactly as TIER_PRECEDENCE declares")
val shuffled = ["gc_async_mut", "nogc_async_mut", "common", "nogc_async_mut_noalloc", "nogc_sync_mut"]
expect(tier_ordered_subdirs(shuffled)).to_equal(TIER_PRECEDENCE)
```

</details>

#### lists all five canonical tiers, so no tier is silently unranked

- lists all five canonical tiers, so no tier is silently unranked
   - Expected: TIER_PRECEDENCE.len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lists all five canonical tiers, so no tier is silently unranked")
expect(TIER_PRECEDENCE.len()).to_equal(5)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/module_resolver/tierless_std_import_order_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering tier_ordered_subdirs — reproducer, tier_ordered_subdirs — detection (must be a permutation).
- tier_ordered_subdirs — reproducer
- tier_ordered_subdirs — detection (must be a permutation)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3e9b0ad41cbcbab52de1b4bf18fe22d51c8724604240ccb408fb21b2dcaea169`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3e9b0ad41cbcbab52de1b4bf18fe22d51c8724604240ccb408fb21b2dcaea169`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3e9b0ad41cbcbab52de1b4bf18fe22d51c8724604240ccb408fb21b2dcaea169`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/module_resolver/tierless_std_import_order_spec.spl
mirror: doc/06_spec/01_unit/compiler/module_resolver/tierless_std_import_order_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/module_resolver/tierless_std_import_order_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/module_resolver/tierless_std_import_order_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/module_resolver/tierless_std_import_order_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/module_resolver/tierless_std_import_order_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'puts common first regardless of the incoming listing order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/module_resolver/tierless_std_import_order_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'yields the SAME order for two different readdir permutations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/module_resolver/tierless_std_import_order_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prefers common over gc_async_mut for a path present in both' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
