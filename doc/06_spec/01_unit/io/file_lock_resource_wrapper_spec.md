# file_lock_resource_wrapper_spec

> Resource wrapper for FileLock — WP-J acceptance

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# file_lock_resource_wrapper_spec

Resource wrapper for FileLock — WP-J acceptance

## At a Glance

| Field | Value |
|-------|-------|
| Category | I/O |
| Status | Active |
| Source | `test/01_unit/io/file_lock_resource_wrapper_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Resource wrapper for FileLock — WP-J acceptance

Tests the new FileLock wrapper class with resource ownership pattern:
- Sentinel-based validity checks
- Consuming close() method
- Double-close guard (one-shot safety)
- Backward compatibility with deprecated file_lock/file_unlock

## Scenarios

### FileLock resource wrapper

#### FileLock.is_valid checks sentinel

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- FileLock.is_valid checks sentinel


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("FileLock.is_valid checks sentinel")
val lock = FileLock(handle: 5)
assert_true(lock.is_valid())
```

</details>

#### FileLock.is_valid detects invalid sentinel (-1)

- FileLock.is_valid detects invalid sentinel (-1)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("FileLock.is_valid detects invalid sentinel (-1)")
val lock = FileLock(handle: -1)
assert_false(lock.is_valid())
```

</details>

#### FileLock sentinel is -1

- FileLock sentinel is -1


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("FileLock sentinel is -1")
val lock = FileLock(handle: -1)
assert_false(lock.is_valid())

# FileLock with 0 should be valid (sentinel is -1, not 0)
val lock_zero = FileLock(handle: 0)
assert_true(lock_zero.is_valid())
```

</details>

### FileLock consuming close with double-close guard

#### close on invalid sentinel is safe

- close on invalid sentinel is safe


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("close on invalid sentinel is safe")
val lock = FileLock(handle: -1)
lock.close()
assert_equal(lock.handle, -1)
# No exception should occur
lock.close()
assert_equal(lock.handle, -1)
```

</details>

### Deprecated file_lock/file_unlock compatibility

#### file_lock (deprecated) still exists and is callable

- file_lock (deprecated) still exists and is callable


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("file_lock (deprecated) still exists and is callable")
# Note: file_lock tries to lock a real file, which may fail.
# This verifies the function is still reachable.
val result = file_lock("/tmp/nonexistent_file_for_test", 1)
# Result could be -1 or a valid fd; just verify it returned something
assert_true(result >= -1)
```

</details>

#### file_unlock (deprecated) still exists and is callable

- file_unlock (deprecated) still exists and is callable


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("file_unlock (deprecated) still exists and is callable")
# Note: file_unlock with invalid fd -1 should return false.
# This verifies the function is still reachable.
val result = file_unlock(-1)
assert_false(result)
```

</details>

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

- Canonical SPipe generation for source `0bdca3b58e74e6ef888d7f6705338e4ee219668b7e4a2455ecdd923ae0dbdbd7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0bdca3b58e74e6ef888d7f6705338e4ee219668b7e4a2455ecdd923ae0dbdbd7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0bdca3b58e74e6ef888d7f6705338e4ee219668b7e4a2455ecdd923ae0dbdbd7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/io/file_lock_resource_wrapper_spec.spl
mirror: doc/06_spec/01_unit/io/file_lock_resource_wrapper_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/io/file_lock_resource_wrapper_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/io/file_lock_resource_wrapper_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/io/file_lock_resource_wrapper_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'FileLock.is_valid checks sentinel' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/io/file_lock_resource_wrapper_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'FileLock.is_valid detects invalid sentinel (-1)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/io/file_lock_resource_wrapper_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'FileLock sentinel is -1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
