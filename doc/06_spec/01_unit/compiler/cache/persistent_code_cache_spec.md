# Persistent Code Cache Specification

> Tests covering persistent code cache — warm start.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Persistent Code Cache Specification

## Scenarios

### persistent code cache — warm start

#### cold start misses on an empty cache root

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- cold start misses on an empty cache root


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cold start misses on an empty cache root")
val root = fresh_root()
val load = pcc_load(root, key_for(SRC))
expect(load.hit).to_be(false)
expect(load.reason).to_be("absent")
```

</details>

#### warm start hits after a cold start stored the prepared form

- warm start hits after a cold start stored the prepared form


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warm start hits after a cold start stored the prepared form")
val root = fresh_root()
val key = key_for(SRC)
expect(pcc_store(root, key, prepare(SRC))).to_be(true)
val warm = pcc_load(root, key)
expect(warm.hit).to_be(true)
expect(warm.reason).to_be("")
```

</details>

#### warm-start words are identical to what the cold start prepared

- warm-start words are identical to what the cold start prepared


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warm-start words are identical to what the cold start prepared")
val root = fresh_root()
val key = key_for(SRC)
val cold = prepare(SRC)
pcc_store(root, key, cold)
val warm = pcc_load(root, key)
expect(words_equal(cold, warm.words)).to_be(true)
expect(warm.words.len()).to_be(cold.len())
```

</details>

#### round-trips an empty prepared form without confusing it with a miss

- round-trips an empty prepared form without confusing it with a miss


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips an empty prepared form without confusing it with a miss")
val root = fresh_root()
val key = pcc_key_new("unit/empty", "h0", "d0")
pcc_store(root, key, [])
val warm = pcc_load(root, key)
expect(warm.hit).to_be(true)
expect(warm.words.len()).to_be(0)
```

</details>

#### round-trips negative and large words

- round-trips negative and large words


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips negative and large words")
val root = fresh_root()
val key = pcc_key_new("unit/wide", "h1", "d0")
val w: [i64] = [0, -1, 42, -9007199254740991, 9007199254740991]
pcc_store(root, key, w)
val warm = pcc_load(root, key)
expect(words_equal(w, warm.words)).to_be(true)
```

</details>

#### keys the entry path by the digest so entries cannot collide

- keys the entry path by the digest so entries cannot collide


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keys the entry path by the digest so entries cannot collide")
val a = pcc_key_digest(key_for(SRC))
val root = fresh_root()
expect(pcc_entry_path(root, a).ends_with(a.substring(2, a.len()))).to_be(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/cache/persistent_code_cache_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering persistent code cache — warm start.
- persistent code cache — warm start

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `148b90ffe0980c760fd447082fa2b158442ad99b13f018deb31385e18aef2db8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `148b90ffe0980c760fd447082fa2b158442ad99b13f018deb31385e18aef2db8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `148b90ffe0980c760fd447082fa2b158442ad99b13f018deb31385e18aef2db8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/cache/persistent_code_cache_spec.spl
mirror: doc/06_spec/01_unit/compiler/cache/persistent_code_cache_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/cache/persistent_code_cache_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/cache/persistent_code_cache_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/cache/persistent_code_cache_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'cold start misses on an empty cache root' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/cache/persistent_code_cache_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'warm start hits after a cold start stored the prepared form' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/cache/persistent_code_cache_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'warm-start words are identical to what the cold start prepared' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
