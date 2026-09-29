# Fixed Map Backing Storage Regression Specification

> Tests covering FixedMap backing storage and behavior after the parallel-array refactor.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fixed Map Backing Storage Regression Specification

## Scenarios

### FixedMap backing storage and behavior after the parallel-array refactor

#### reserves backing arrays once at construction and never grows or shrinks them

- reserves backing arrays once at construction and never grows or shrinks them
   - Expected: map.keys.len() equals `8`
   - Expected: map.values.len() equals `8`
   - Expected: map.occupied.len() equals `8`
   - Expected: map.keys.len() equals `8`
   - Expected: map.values.len() equals `8`
   - Expected: map.occupied.len() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reserves backing arrays once at construction and never grows or shrinks them")
val map = FixedMap.new(8)
expect(map.keys.len()).to_equal(8)
expect(map.values.len()).to_equal(8)
expect(map.occupied.len()).to_equal(8)

map.put(1, 100)
map.put(2, 200)
map.remove(1)
expect(map.keys.len()).to_equal(8)
expect(map.values.len()).to_equal(8)
expect(map.occupied.len()).to_equal(8)
```

</details>

#### still stores, retrieves, updates, and removes correctly

- still stores, retrieves, updates, and removes correctly
   - Expected: map.get(42) equals `100`
   - Expected: map.get(7) equals `200`
   - Expected: map.get(42) equals `999`
   - Expected: map.size() equals `2`
   - Expected: map does not contain `42`
   - Expected: map.get(7) equals `200`
   - Expected: map.size() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("still stores, retrieves, updates, and removes correctly")
val map = FixedMap.new(16)
map.put(42, 100)
map.put(7, 200)
expect(map.get(42)).to_equal(100)
expect(map.get(7)).to_equal(200)

map.put(42, 999)
expect(map.get(42)).to_equal(999)
expect(map.size()).to_equal(2)

assert_true(map.contains(42))
assert_true(map.remove(42))
expect(map.contains(42)).to_equal(false)
expect(map.get(7)).to_equal(200)
expect(map.size()).to_equal(1)
```

</details>

#### still rejects put past capacity (unaffected by this fix, checked for completeness)

- still rejects put past capacity (unaffected by this fix, checked for completeness)
   - Expected: map.put(3, 30) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("still rejects put past capacity (unaffected by this fix, checked for completeness)")
val map = FixedMap.new(2)
assert_true(map.put(1, 10))
assert_true(map.put(2, 20))
expect(map.put(3, 30)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut_noalloc/collections/fixed_map_backing_storage_regression_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering FixedMap backing storage and behavior after the parallel-array refactor.
- FixedMap backing storage and behavior after the parallel-array refactor

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

- Canonical SPipe generation for source `fe2fd232b67b3666dcc05fb5a796760a5e820cb2513f85b29df82f445d121f79`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fe2fd232b67b3666dcc05fb5a796760a5e820cb2513f85b29df82f445d121f79`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fe2fd232b67b3666dcc05fb5a796760a5e820cb2513f85b29df82f445d121f79`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/nogc_async_mut_noalloc/collections/fixed_map_backing_storage_regression_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut_noalloc/collections/fixed_map_backing_storage_regression_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut_noalloc/collections/fixed_map_backing_storage_regression_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut_noalloc/collections/fixed_map_backing_storage_regression_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut_noalloc/collections/fixed_map_backing_storage_regression_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_async_mut_noalloc/collections/fixed_map_backing_storage_regression_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reserves backing arrays once at construction and never grows or shrinks them' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut_noalloc/collections/fixed_map_backing_storage_regression_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still stores, retrieves, updates, and removes correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut_noalloc/collections/fixed_map_backing_storage_regression_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still rejects put past capacity (unaffected by this fix, checked for completeness)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
