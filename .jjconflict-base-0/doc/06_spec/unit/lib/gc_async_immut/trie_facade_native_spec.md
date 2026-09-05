# Trie Facade Native Specification

> Tests covering gc_async_immut PersistentTrie package native backend.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Trie Facade Native Specification

## Scenarios

### gc_async_immut PersistentTrie package native backend

#### stores shared-prefix package-facade entries

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- stores shared-prefix package-facade entries
   - Expected: trie.len() equals `2`
   - Expected: trie.get("app") equals `1`
   - Expected: trie.get("apple") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores shared-prefix package-facade entries")
val trie = PersistentTrie.empty().set("app", 1).set("apple", 2)

expect(trie.len()).to_equal(2)
expect(trie.get("app")).to_equal(1)
expect(trie.get("apple")).to_equal(2)
```

</details>

#### overwrites package-facade entries

- overwrites package-facade entries
   - Expected: trie.get("app") equals `1`
   - Expected: overwritten.get("app") equals `3`
   - Expected: overwritten.get("apple") equals `2`
   - Expected: overwritten.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("overwrites package-facade entries")
val trie = PersistentTrie.empty().set("app", 1).set("apple", 2)
val overwritten = trie.set("app", 3)

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
| Source | `test/unit/lib/gc_async_immut/trie_facade_native_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gc_async_immut PersistentTrie package native backend.
- gc_async_immut PersistentTrie package native backend

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `b4e5ee1234d5f6bc12bcfea4cf170e31cde873f95822b47f37b71a61f355c64e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b4e5ee1234d5f6bc12bcfea4cf170e31cde873f95822b47f37b71a61f355c64e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b4e5ee1234d5f6bc12bcfea4cf170e31cde873f95822b47f37b71a61f355c64e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/gc_async_immut/trie_facade_native_spec.spl
mirror: doc/06_spec/unit/lib/gc_async_immut/trie_facade_native_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/gc_async_immut/trie_facade_native_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/gc_async_immut/trie_facade_native_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/gc_async_immut/trie_facade_native_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/gc_async_immut/trie_facade_native_spec.spl:11:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stores shared-prefix package-facade entries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gc_async_immut/trie_facade_native_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'overwrites package-facade entries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
