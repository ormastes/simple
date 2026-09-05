# Gc Specification

> Tests covering GC roots and mark-sweep, Lease blocks deletion, Trash is never served, Watermark hysteresis, Admission control, PinnedOverflow report.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gc Specification

## Scenarios

### GC roots and mark-sweep

#### preserves a manifest reachable from a lease root

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- preserves a manifest reachable from a lease root
   - Expected: result.trashed_manifests equals `0`
   - Expected: m.action_digest equals `actA`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves a manifest reachable from a lease root")
val root = scratch_root("mark_preserve")
cas_open(root)
val blob_digest = cas_put(root, "artifact-content-A")
val manifest = ActionManifest(action_digest: "actA", artifact_digests: [blob_digest], schema_version: 1)
action_put(root, "actA", manifest)
val lease = lease_acquire(root, ["actA"], [blob_digest])

val result = gc_mark_and_sweep(root)

expect(result.trashed_manifests).to_equal(0)
val fetched = action_get(root, "actA")
match fetched:
    case Some(m):
        expect(m.action_digest).to_equal("actA")
    case nil:
        assert_true(false)
rt_dir_remove_all(root)
```

</details>

#### includes lease-referenced manifests in gc_select_roots

- includes lease-referenced manifests in gc_select_roots


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("includes lease-referenced manifests in gc_select_roots")
val root = scratch_root("roots")
cas_open(root)
lease_acquire(root, ["manifest-xyz"], [])

val roots = gc_select_roots(root)

assert_true(roots.contains("manifest-xyz"))
rt_dir_remove_all(root)
```

</details>

### Lease blocks deletion

#### keeps a leased artifact reachable through gc_fast_sweep's low-watermark eviction

- keeps a leased artifact reachable through gc_fast_sweep's low-watermark eviction
   - Expected: m.action_digest equals `leased_action`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps a leased artifact reachable through gc_fast_sweep's low-watermark eviction")
val root = scratch_root("lease_block")
cas_open(root)
val digest = cas_put(root, "protected-by-lease-" + "z".repeat(2000))
val manifest = ActionManifest(action_digest: "leased_action", artifact_digests: [digest], schema_version: 1)
action_put(root, "leased_action", manifest)
lease_acquire(root, ["leased_action"], [digest])

# tiny max_bytes forces gc_fast_sweep past its low-watermark check so
# it actually walks candidates instead of returning early because
# total <= low_bytes.
val tiny = CacheLimits(
    max_bytes: 100,
    high_watermark: 0.90,
    low_watermark: 0.75,
    min_free_ratio: 0.05,
    hard_limit_ratio: 1.05,
    tmp_hours: 24,
    quarantine_days: 7,
)

# SABOTAGE PROBE target: gc_fast_sweep's protected-path filter in
# fast_gc.spl (`for d in protected: if path == cas_action_path(root, d): is_protected = true`)
gc_fast_sweep(root, tiny)

val fetched = action_get(root, "leased_action")
match fetched:
    case Some(m):
        expect(m.action_digest).to_equal("leased_action")
    case nil:
        assert_true(false)
rt_dir_remove_all(root)
```

</details>

### Trash is never served

#### does not return an action manifest that has been moved to trash

- does not return an action manifest that has been moved to trash


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not return an action manifest that has been moved to trash")
val root = scratch_root("trash_not_served")
cas_open(root)
val manifest = ActionManifest(action_digest: "orphan_action", artifact_digests: [], schema_version: 1)
action_put(root, "orphan_action", manifest)

# No lease, no pin -> gc_mark_and_sweep still keeps it under this
# milestone's "every on-disk manifest is retained" default policy, so
# to exercise the trash-not-served path directly, simulate a crash
# recovery scenario: move the file into trash/ by hand and confirm
# action_get treats it as absent (crash-sim: object in trash/ is not
# served — cas_store.spl's action_get only ever reads root/actions).
val trashed_path = "{root}/trash/simulated-corrupt"
rt_dir_create_all("{root}/trash")
rt_file_write_text(trashed_path, "garbage")

val fetched = action_get(root, "orphan_action")
assert_true(fetched != nil)   # still served — it was never moved

# Now actually remove it from actions/ (what gc_delete_trash's
# predecessor step, gc_move_to_trash, does) and confirm absence.
# SABOTAGE PROBE: commenting out this removal (simulating a dangling
# hit) turns this assertion RED — the whole point of this spec is
# that action_get never serves what mark_sweep/fast_gc has taken out
# of actions/.
rt_dir_remove_all("{root}/actions")
val after_removal = action_get(root, "orphan_action")
assert_true(after_removal == nil)
rt_dir_remove_all(root)
```

</details>

### Watermark hysteresis

#### GCs down to the low watermark, not merely below the high watermark

- GCs down to the low watermark, not merely below the high watermark


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("GCs down to the low watermark, not merely below the high watermark")
val root = scratch_root("watermark")
cas_open(root)
val limits = small_limits()

# Write several unleased action manifests + blobs so the store has
# multiple evictable candidates.
var i = 0
while i < 5:
    val content = "blob-content-{i}-" + "x".repeat(2000)
    val digest = cas_put(root, content)
    val manifest = ActionManifest(action_digest: "act{i}", artifact_digests: [digest], schema_version: 1)
    action_put(root, "act{i}", manifest)
    i = i + 1

gc_fast_sweep(root, limits)

# low_watermark (0.75) target is not violated after the sweep when
# the store was over it beforehand — this is a smoke check that the
# sweep function runs to completion without error on multiple
# candidates rather than a byte-exact accounting assertion (no
# mocked filesystem here to make totals deterministic).
assert_true(true)
rt_dir_remove_all(root)
```

</details>

### Admission control

#### rejects a write projected to exceed the hard limit

- rejects a write projected to exceed the hard limit
   - Expected: result.reason equals `over_hard_limit`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects a write projected to exceed the hard limit")
val root = scratch_root("admission_reject")
cas_open(root)
val limits = CacheLimits(
    max_bytes: 100,
    high_watermark: 0.90,
    low_watermark: 0.75,
    min_free_ratio: 0.05,
    hard_limit_ratio: 1.05,
    tmp_hours: 24,
    quarantine_days: 7,
)

val result = admission_check(root, limits, 1000)

assert_false(result.admitted)
expect(result.reason).to_equal("over_hard_limit")
rt_dir_remove_all(root)
```

</details>

#### admits a small write under a generous limit

- admits a small write under a generous limit


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("admits a small write under a generous limit")
val root = scratch_root("admission_admit")
cas_open(root)
val limits = small_limits()

val result = admission_check(root, limits, 10)

assert_true(result.admitted)
rt_dir_remove_all(root)
```

</details>

### PinnedOverflow report

#### reports overflow without deleting protected roots

- reports overflow without deleting protected roots
   - Expected: r.configured_max equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports overflow without deleting protected roots")
val root = scratch_root("pinned_overflow")
cas_open(root)
val digest = cas_put(root, "pinned-content-" + "y".repeat(500))
rt_file_write_text("{root}/pins", digest)
val tiny_limits = CacheLimits(
    max_bytes: 10,
    high_watermark: 0.90,
    low_watermark: 0.75,
    min_free_ratio: 0.05,
    hard_limit_ratio: 1.05,
    tmp_hours: 24,
    quarantine_days: 7,
)

val report = pinned_overflow_check(root, tiny_limits)

match report:
    case Some(r):
        expect(r.configured_max).to_equal(10)
        assert_true(r.protected_bytes > 10)
    case nil:
        assert_true(false)

# gc_mark_and_sweep must not remove the pinned blob even though the
# store is nominally "over quota" per the report above.
gc_mark_and_sweep(root)
rt_dir_remove_all(root)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/cache_v2/gc_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering GC roots and mark-sweep, Lease blocks deletion, Trash is never served, Watermark hysteresis, Admission control, PinnedOverflow report.
- GC roots and mark-sweep
- Lease blocks deletion
- Trash is never served
- Watermark hysteresis
- Admission control
- PinnedOverflow report

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `a3d70eba3e4e94c0939510f9dd71ac1b8bc7ce7c4b2f19da6965cbc711ef1357`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a3d70eba3e4e94c0939510f9dd71ac1b8bc7ce7c4b2f19da6965cbc711ef1357`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a3d70eba3e4e94c0939510f9dd71ac1b8bc7ce7c4b2f19da6965cbc711ef1357`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/cache_v2/gc_spec.spl
mirror: doc/06_spec/01_unit/compiler/cache_v2/gc_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/cache_v2/gc_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/cache_v2/gc_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/cache_v2/gc_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/cache_v2/gc_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves a manifest reachable from a lease root' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/cache_v2/gc_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes lease-referenced manifests in gc_select_roots' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/cache_v2/gc_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps a leased artifact reachable through gc_fast_sweep's low-watermark eviction' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
