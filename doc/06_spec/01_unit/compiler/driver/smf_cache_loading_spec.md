# Smf Cache Loading Specification

> Tests covering SMF cache lookup, SMF freshness check for interpreter, SMF cache fallback logic.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Smf Cache Loading Specification

## Scenarios

### SMF cache lookup

#### finds cached entry by source path

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- finds cached entry by source path
   - Expected: entry != nil is true
   - Expected: entry.unwrap().smf_path equals `build/smf/src_main.smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("finds cached entry by source path")
var cache = mock_cache_new()
cache = mock_cache_add(cache, "src/main.spl", "build/smf/src_main.smf", 42)
val entry = mock_cache_find(cache, "src/main.spl")
expect(entry != nil).to_equal(true)
expect(entry.unwrap().smf_path).to_equal("build/smf/src_main.smf")
```

</details>

#### returns nil for missing source path

- returns nil for missing source path
   - Expected: entry != nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns nil for missing source path")
val cache = mock_cache_new()
val entry = mock_cache_find(cache, "src/missing.spl")
expect(entry != nil).to_equal(false)
```

</details>

#### finds correct entry among multiple

- finds correct entry among multiple
   - Expected: entry != nil is true
   - Expected: entry.unwrap().source_hash equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("finds correct entry among multiple")
var cache = mock_cache_new()
cache = mock_cache_add(cache, "src/a.spl", "build/smf/a.smf", 10)
cache = mock_cache_add(cache, "src/b.spl", "build/smf/b.smf", 20)
cache = mock_cache_add(cache, "src/c.spl", "build/smf/c.smf", 30)
val entry = mock_cache_find(cache, "src/b.spl")
expect(entry != nil).to_equal(true)
expect(entry.unwrap().source_hash).to_equal(20)
```

</details>

### SMF freshness check for interpreter

#### returns FRESH when hashes match

- returns FRESH when hashes match
   - Expected: result equals `MOCK_FRESH`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns FRESH when hashes match")
val result = mock_validate(42, 42)
expect(result).to_equal(MOCK_FRESH)
```

</details>

#### returns STALE when hashes differ

- returns STALE when hashes differ
   - Expected: result equals `MOCK_STALE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns STALE when hashes differ")
val result = mock_validate(42, 99)
expect(result).to_equal(MOCK_STALE)
```

</details>

#### returns MISSING when cached hash is zero

- returns MISSING when cached hash is zero
   - Expected: result equals `MOCK_MISSING`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns MISSING when cached hash is zero")
val result = mock_validate(42, 0)
expect(result).to_equal(MOCK_MISSING)
```

</details>

### SMF cache fallback logic

#### loads from cache when fresh

- loads from cache when fresh
   - Expected: use_smf is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("loads from cache when fresh")
var cache = mock_cache_new()
cache = mock_cache_add(cache, "src/main.spl", "build/smf/main.smf", 100)
val entry = mock_cache_find(cache, "src/main.spl")
val status = mock_validate(100, entry.unwrap().source_hash)
# When FRESH, we load from SMF (not fallback)
val use_smf = status == MOCK_FRESH
expect(use_smf).to_equal(true)
```

</details>

#### falls back to interpreter when stale

- falls back to interpreter when stale
   - Expected: use_smf is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("falls back to interpreter when stale")
var cache = mock_cache_new()
cache = mock_cache_add(cache, "src/main.spl", "build/smf/main.smf", 100)
val entry = mock_cache_find(cache, "src/main.spl")
# Source changed (hash 200 != cached 100)
val status = mock_validate(200, entry.unwrap().source_hash)
val use_smf = status == MOCK_FRESH
expect(use_smf).to_equal(false)
```

</details>

#### falls back to interpreter when not in cache

- falls back to interpreter when not in cache
   - Expected: use_smf is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("falls back to interpreter when not in cache")
val cache = mock_cache_new()
val entry = mock_cache_find(cache, "src/main.spl")
val use_smf = entry.?
expect(use_smf).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/smf_cache_loading_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SMF cache lookup, SMF freshness check for interpreter, SMF cache fallback logic.
- SMF cache lookup
- SMF freshness check for interpreter
- SMF cache fallback logic

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `8b217b292e1b72795e5580117d6813a5354e02079a06a19a3ba05e660eaddebb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8b217b292e1b72795e5580117d6813a5354e02079a06a19a3ba05e660eaddebb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8b217b292e1b72795e5580117d6813a5354e02079a06a19a3ba05e660eaddebb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/driver/smf_cache_loading_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/smf_cache_loading_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/driver/smf_cache_loading_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/smf_cache_loading_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/smf_cache_loading_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/driver/smf_cache_loading_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds cached entry by source path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/smf_cache_loading_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns nil for missing source path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/smf_cache_loading_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds correct entry among multiple' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
