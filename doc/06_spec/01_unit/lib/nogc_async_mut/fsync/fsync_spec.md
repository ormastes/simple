# fsync_spec

> Purpose: Verify the futex-backed fsync mutex lock/unlock state transitions and

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# fsync_spec

Purpose: Verify the futex-backed fsync mutex lock/unlock state transitions and

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/fsync/fsync_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Verify the futex-backed fsync mutex lock/unlock state transitions and
address independence.
Audience: runtime engineers who own std.nogc_async_mut.fsync.

## Scenarios

### fsync mutex/condvar

#### lock and unlock on address 0 complete without error

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lock and unlock on address 0 complete without error
   - Expected: fsync_mutex_is_locked(addr) is true
   - Expected: fsync_mutex_is_locked(addr) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("lock and unlock on address 0 complete without error")
val addr: u32 = 0
fsync_mutex_lock(addr)
# oracle: interpreter-mode acquisition must mark the futex row locked
expect(fsync_mutex_is_locked(addr)).to_equal(true)
fsync_mutex_unlock(addr)
expect(fsync_mutex_is_locked(addr)).to_equal(false)
```

</details>

#### lock and unlock on non-zero address complete without error

- lock and unlock on non-zero address complete without error
   - Expected: fsync_mutex_is_locked(addr) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("lock and unlock on non-zero address complete without error")
val addr: u32 = 42
fsync_mutex_lock(addr)
fsync_mutex_unlock(addr)
# oracle: release clears the lock state on a real address row
expect(fsync_mutex_is_locked(addr)).to_equal(false)
```

</details>

#### multiple lock/unlock pairs on different addresses do not interfere

- multiple lock/unlock pairs on different addresses do not interfere
   - Expected: fsync_mutex_is_locked(b) is true
   - Expected: fsync_mutex_is_locked(a) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("multiple lock/unlock pairs on different addresses do not interfere")
val a: u32 = 1
val b: u32 = 2
fsync_mutex_lock(a)
fsync_mutex_lock(b)
# oracle: address rows are independent — b locked while a locked
expect(fsync_mutex_is_locked(b)).to_equal(true)
fsync_mutex_unlock(b)
fsync_mutex_unlock(a)
expect(fsync_mutex_is_locked(a)).to_equal(false)
```

</details>

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

- Canonical SPipe generation for source `49b70b80736cebe65bb7948a09aeba3b30518b534aef7e572bfd60d892c41701`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `49b70b80736cebe65bb7948a09aeba3b30518b534aef7e572bfd60d892c41701`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `49b70b80736cebe65bb7948a09aeba3b30518b534aef7e572bfd60d892c41701`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_async_mut/fsync/fsync_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/fsync/fsync_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/fsync/fsync_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/fsync/fsync_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/fsync/fsync_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lock and unlock on address 0 complete without error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/fsync/fsync_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lock and unlock on non-zero address complete without error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/fsync/fsync_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'multiple lock/unlock pairs on different addresses do not interfere' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
