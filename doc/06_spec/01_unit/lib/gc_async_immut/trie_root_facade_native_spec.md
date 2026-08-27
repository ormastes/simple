# Trie Root Facade Native Specification

> Tests covering gc_async_immut PersistentTrie root native backend.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Trie Root Facade Native Specification

## Scenarios

### gc_async_immut PersistentTrie root native backend

#### stores shared-prefix root-facade entries through chained calls

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- stores shared-prefix root-facade entries through chained calls
   - Expected: trie.len() equals `2`
   - Expected: trie.get("app") equals `1`
   - Expected: trie.get("apple") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("stores shared-prefix root-facade entries through chained calls")
val trie = PersistentTrie.empty().set("app", 1).set("apple", 2)

expect(trie.len()).to_equal(2)
expect(trie.get("app")).to_equal(1)
expect(trie.get("apple")).to_equal(2)
```

</details>

#### stores shared-prefix root-facade entries with typed receivers

- stores shared-prefix root-facade entries with typed receivers
   - Expected: trie.len() equals `2`
   - Expected: trie.get("app") equals `1`
   - Expected: trie.get("apple") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("stores shared-prefix root-facade entries with typed receivers")
val base: PersistentTrie = PersistentTrie.empty()
val trie: PersistentTrie = base.set("app", 1).set("apple", 2)

expect(trie.len()).to_equal(2)
expect(trie.get("app")).to_equal(1)
expect(trie.get("apple")).to_equal(2)
```

</details>

#### overwrites root-facade entries with typed receivers

- overwrites root-facade entries with typed receivers
   - Expected: trie.get("app") equals `1`
   - Expected: overwritten.get("app") equals `3`
   - Expected: overwritten.get("apple") equals `2`
   - Expected: overwritten.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("overwrites root-facade entries with typed receivers")
val base: PersistentTrie = PersistentTrie.empty()
val trie: PersistentTrie = base.set("app", 1).set("apple", 2)
val overwritten: PersistentTrie = trie.set("app", 3)

expect(trie.get("app")).to_equal(1)
expect(overwritten.get("app")).to_equal(3)
expect(overwritten.get("apple")).to_equal(2)
expect(overwritten.len()).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_immut/trie_root_facade_native_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gc_async_immut PersistentTrie root native backend.
- gc_async_immut PersistentTrie root native backend

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

- Canonical SPipe generation for source `f58dd14afaa16a4c5288fdb527d6c168b18e34676b99e966c949cf35bae493b2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f58dd14afaa16a4c5288fdb527d6c168b18e34676b99e966c949cf35bae493b2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f58dd14afaa16a4c5288fdb527d6c168b18e34676b99e966c949cf35bae493b2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/gc_async_immut/trie_root_facade_native_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_immut/trie_root_facade_native_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_immut/trie_root_facade_native_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_immut/trie_root_facade_native_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_immut/trie_root_facade_native_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_immut/trie_root_facade_native_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stores shared-prefix root-facade entries through chained calls' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_immut/trie_root_facade_native_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stores shared-prefix root-facade entries with typed receivers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_immut/trie_root_facade_native_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'overwrites root-facade entries with typed receivers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
