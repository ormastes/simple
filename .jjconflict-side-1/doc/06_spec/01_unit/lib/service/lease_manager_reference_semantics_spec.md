# Similar-Problem Detection: Mutation Through a By-Value Spec Helper

> Generalizes the defect class in

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Similar-Problem Detection: Mutation Through a By-Value Spec Helper

Generalizes the defect class in

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/service/lease_manager_reference_semantics_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Generalizes the defect class in
doc/08_tracking/bug/spec_value_type_helper_mutates_copy_family_2026-08-10.md:
a helper that takes the subject BY VALUE mutates a throwaway copy, so every
absence assertion afterwards ("no lease is held", "the queue is empty") is
vacuously true and tests nothing.

`src/lib/nogc_sync_mut/service/lease_manager.spl` is the canonical case:
`LeaseManager` was a `struct` mutated through free `fn`s, so `next_id` never
advanced and `leases` never grew. It is now a `class` (reference type).

Oracle shape that catches the whole class: pass the subject through an
INDIRECT helper (a plain `fn` taking it by value, exactly the shape that
used to lose the write), then assert the mutation is visible through the
ORIGINAL binding. A copy-semantics regression makes the presence assertions
fail -- and, crucially, the absence assertions here are paired with presence
assertions so a vacuous "nothing is held" can never pass alone.

## Scenarios

### lease manager mutation survives a by-value helper boundary

#### makes a lease taken inside a by-value helper visible to the caller

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- makes a lease taken inside a by-value helper visible to the caller


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("makes a lease taken inside a by-value helper visible to the caller")
var mgr = lease_manager_new()
# Paired baseline: prove the absence assertion is not vacuous by
# showing the SAME assertion flips after the mutation.
assert_equal(active_lease_count(mgr), 0i64)
val result = helper_take_exclusive(mgr, rt_getpid())
assert_true(result.ok)
assert_equal(active_lease_count(mgr), 1i64)
assert_true(has_active_exclusive(mgr))
```

</details>

#### blocks a second exclusive acquire taken through the helper

- blocks a second exclusive acquire taken through the helper


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocks a second exclusive acquire taken through the helper")
var mgr = lease_manager_new()
val first = helper_take_exclusive(mgr, rt_getpid())
assert_true(first.ok)
val second = helper_take_exclusive(mgr, rt_getpid())
# A lost write would make this `true` -- the false-success shape.
assert_false(second.ok)
assert_contains(second.busy_message, "BUSY")
```

</details>

#### advances the id counter across a by-value helper boundary

- advances the id counter across a by-value helper boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("advances the id counter across a by-value helper boundary")
var mgr = lease_manager_new()
val first = helper_take_exclusive(mgr, rt_getpid())
val released = helper_release(mgr, first.lease_id)
assert_true(released)
val second = helper_take_exclusive(mgr, rt_getpid())
# next_id living on a copy gave EVERY lease the id `lease-1`.
val fid = first.lease_id
val sid = second.lease_id
assert_not_equal(fid, sid)
```

</details>

#### restores availability through the by-value release helper

- restores availability through the by-value release helper


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("restores availability through the by-value release helper")
var mgr = lease_manager_new()
val first = helper_take_exclusive(mgr, rt_getpid())
assert_equal(active_lease_count(mgr), 1i64)
val released = helper_release(mgr, first.lease_id)
assert_true(released)
assert_equal(active_lease_count(mgr), 0i64)
assert_false(has_active_exclusive(mgr))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `07bf2aceda57201dc1bd2d4a1828ace90e2a673f59c83c74e078888207917289`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `07bf2aceda57201dc1bd2d4a1828ace90e2a673f59c83c74e078888207917289`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `07bf2aceda57201dc1bd2d4a1828ace90e2a673f59c83c74e078888207917289`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/service/lease_manager_reference_semantics_spec.spl
mirror: doc/06_spec/01_unit/lib/service/lease_manager_reference_semantics_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/service/lease_manager_reference_semantics_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/service/lease_manager_reference_semantics_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/service/lease_manager_reference_semantics_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'makes a lease taken inside a by-value helper visible to the caller' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/service/lease_manager_reference_semantics_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'blocks a second exclusive acquire taken through the helper' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/service/lease_manager_reference_semantics_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'advances the id counter across a by-value helper boundary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
