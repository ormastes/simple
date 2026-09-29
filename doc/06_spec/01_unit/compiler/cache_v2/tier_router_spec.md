# Tier Router Specification

> Tests covering TierRouter.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tier Router Specification

## Scenarios

### TierRouter

#### misses on an unknown action digest

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- misses on an unknown action digest


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("misses on an unknown action digest")
val ws = fresh_workspace("miss")
val tr = tier_router_open(ws)
val result = tier_router_lookup(tr, CacheNamespace.WorkspaceLocal, "no-such-digest")
match result:
    case TierLookupResult.Miss:
        assert_true(true)
    case _:
        assert_true(false)
```

</details>

#### hits L1 after a publish, with the same content

- hits L1 after a publish, with the same content
   - Expected: hit.action_digest equals `action-l1`
   - Expected: hit.artifact_digests.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("hits L1 after a publish, with the same content")
val ws = fresh_workspace("l1hit")
val tr = tier_router_open(ws)
val artifact = cas_put(tr.l1_root, "artifact-body-l1")
val m = make_manifest("action-l1", [artifact])
val published = tier_router_publish(tr, CacheNamespace.WorkspaceLocal, "action-l1", m)
match published:
    case TierPublishResult.Published:
        assert_true(true)
    case _:
        assert_true(false)
val result = tier_router_lookup(tr, CacheNamespace.WorkspaceLocal, "action-l1")
match result:
    case TierLookupResult.HitL1(hit):
        expect(hit.action_digest).to_equal("action-l1")
        expect(hit.artifact_digests.len()).to_equal(1)
    case _:
        assert_true(false)
```

</details>

#### hits L2 and backfills into L1

- hits L2 and backfills into L1
   - Expected: put_ok is true
   - Expected: cas_has(tr.l1_root, artifact) is false
   - Expected: hit.action_digest equals `action-l2`
   - Expected: cas_has(tr.l1_root, artifact) is true
   - Expected: hit2.action_digest equals `action-l2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("hits L2 and backfills into L1")
val ws = fresh_workspace("l2hit")
val tr = tier_router_open(ws)
# Publish directly into L2 (simulating a prior machine-tier build)
# by constructing a second router pointed at the same L2 root but a
# DIFFERENT L1, so the L1 side starts genuinely empty.
val artifact = cas_put(tr.l2_root, "artifact-body-l2")
val m = make_manifest("action-l2", [artifact])
# Manually publish into L2's action index + manifest store the same
# way tier_router_publish does for L1: reuse cas_store directly.
val put_ok = result_manifest_put(tr.l2_root, "action-l2", m)
expect(put_ok).to_equal(true)
action_index_put(tr.l2_root, CacheNamespace.WorkspaceLocal, "action-l2", result_manifest_digest(m))
expect(cas_has(tr.l1_root, artifact)).to_equal(false)
val result = tier_router_lookup(tr, CacheNamespace.WorkspaceLocal, "action-l2")
match result:
    case TierLookupResult.HitL2Backfilled(hit):
        expect(hit.action_digest).to_equal("action-l2")
    case _:
        assert_true(false)
expect(cas_has(tr.l1_root, artifact)).to_equal(true)
# Second lookup is now an L1 hit.
val result2 = tier_router_lookup(tr, CacheNamespace.WorkspaceLocal, "action-l2")
match result2:
    case TierLookupResult.HitL1(hit2):
        expect(hit2.action_digest).to_equal("action-l2")
    case _:
        assert_true(false)
```

</details>

#### rejects publish when the artifact closure is incomplete

- rejects publish when the artifact closure is incomplete


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects publish when the artifact closure is incomplete")
val ws = fresh_workspace("closure")
val tr = tier_router_open(ws)
# "missing-artifact" was never cas_put into L1.
val m = make_manifest("action-closure", ["missing-artifact"])
val result = tier_router_publish(tr, CacheNamespace.WorkspaceLocal, "action-closure", m)
match result:
    case TierPublishResult.ClosureIncomplete:
        assert_true(true)
    case _:
        assert_true(false)
```

</details>

#### detects a conflicting publish under the same action digest

- detects a conflicting publish under the same action digest


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("detects a conflicting publish under the same action digest")
val ws = fresh_workspace("conflict")
val tr = tier_router_open(ws)
val a1 = cas_put(tr.l1_root, "artifact-one")
val a2 = cas_put(tr.l1_root, "artifact-two")
val m1 = make_manifest("action-conflict", [a1])
val first = tier_router_publish(tr, CacheNamespace.WorkspaceLocal, "action-conflict", m1)
match first:
    case TierPublishResult.Published:
        assert_true(true)
    case _:
        assert_true(false)
val m2 = make_manifest("action-conflict", [a2])
val second = tier_router_publish(tr, CacheNamespace.WorkspaceLocal, "action-conflict", m2)
match second:
    case TierPublishResult.Conflict(existing, attempted):
        assert_true(existing != attempted)
    case _:
        assert_true(false)
```

</details>

#### treats a corrupted L1 blob as a miss, never serving unverified bytes

- treats a corrupted L1 blob as a miss, never serving unverified bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("treats a corrupted L1 blob as a miss, never serving unverified bytes")
val ws = fresh_workspace("corrupt")
val tr = tier_router_open(ws)
val artifact = cas_put(tr.l1_root, "artifact-corruptible")
val m = make_manifest("action-corrupt", [artifact])
tier_router_publish(tr, CacheNamespace.WorkspaceLocal, "action-corrupt", m)
# Corrupt the underlying blob in place so its bytes no longer hash
# to the requested digest.
val blob_path = "{tr.l1_root}/cas/sha256/{artifact.substring(0, 2)}/{artifact.substring(2, artifact.len())}"
rt_file_write_text(blob_path, "TAMPERED")
val fetched = cas_get(tr.l1_root, artifact)
match fetched:
    case Some(_):
        assert_true(false)
    case nil:
        assert_true(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/cache_v2/tier_router_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering TierRouter.
- TierRouter

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `08d47b6457cb97c3b9975a56bb4aa8c2f8cebc5483021a5e2b6bc3569c38db27`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `08d47b6457cb97c3b9975a56bb4aa8c2f8cebc5483021a5e2b6bc3569c38db27`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `08d47b6457cb97c3b9975a56bb4aa8c2f8cebc5483021a5e2b6bc3569c38db27`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/cache_v2/tier_router_spec.spl
mirror: doc/06_spec/01_unit/compiler/cache_v2/tier_router_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/cache_v2/tier_router_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/cache_v2/tier_router_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/cache_v2/tier_router_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/cache_v2/tier_router_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'misses on an unknown action digest' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/cache_v2/tier_router_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hits L1 after a publish, with the same content' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/cache_v2/tier_router_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hits L2 and backfills into L1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
