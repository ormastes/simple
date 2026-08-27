# Atomic Lock via O_EXCL Specification

> Tests that rt_file_create_excl provides atomic file creation semantics,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Atomic Lock via O_EXCL Specification

Tests that rt_file_create_excl provides atomic file creation semantics,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Failing (no implementation yet) |
| Source | `test/03_system/stdlib/database/atomic_lock_excl_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

**ACs:** AC-5 (hardening fix), AC-7 (new tests)
Tests that rt_file_create_excl provides atomic file creation semantics,
and that FileLock.try_create_lock uses it to prevent TOCTOU race conditions.

## Scenarios

### rt_file_create_excl

### basic semantics

#### creates file and returns true when file does not exist

- creates file and returns true when file does not exist
   - Expected: result is true
   - Expected: rt_file_exists(path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates file and returns true when file does not exist")
val path = "/tmp/simple_db_test_excl_create.lock"
cleanup_lock(path)
val result = rt_file_create_excl(path, "pid:12345")
expect(result).to_equal(true)
expect(rt_file_exists(path)).to_equal(true)
cleanup_lock(path)
```

</details>

#### returns false when file already exists

- returns false when file already exists
   - Expected: first is true
   - Expected: second is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns false when file already exists")
val path = "/tmp/simple_db_test_excl_exists.lock"
cleanup_lock(path)
# First create succeeds
val first = rt_file_create_excl(path, "pid:111")
expect(first).to_equal(true)
# Second create must fail (O_EXCL semantics)
val second = rt_file_create_excl(path, "pid:222")
expect(second).to_equal(false)
cleanup_lock(path)
```

</details>

#### writes content to created file

- writes content to created file
   - Expected: rt_file_exists(path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("writes content to created file")
val path = "/tmp/simple_db_test_excl_content.lock"
cleanup_lock(path)
rt_file_create_excl(path, "test_content_here")
expect(rt_file_exists(path)).to_equal(true)
cleanup_lock(path)
```

</details>

### edge cases

#### handles empty content

- handles empty content
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles empty content")
val path = "/tmp/simple_db_test_excl_empty.lock"
cleanup_lock(path)
val result = rt_file_create_excl(path, "")
expect(result).to_equal(true)
cleanup_lock(path)
```

</details>

#### returns false for invalid directory path

- returns false for invalid directory path
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns false for invalid directory path")
val result = rt_file_create_excl("/nonexistent_dir_abc/test.lock", "x")
expect(result).to_equal(false)
```

</details>

### FileLock with O_EXCL

#### sequential lock on same path: first succeeds, second fails

- sequential lock on same path: first succeeds, second fails
   - Expected: acquired is true
   - Expected: second is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sequential lock on same path: first succeeds, second fails")
val path = test_lock_path()
cleanup_lock(path)
cleanup_lock(path + ".lock")
val lock1 = FileLock.for_file(path)
val acquired = lock1.acquire()
expect(acquired).to_equal(true)
# Second lock attempt on same path must fail (short timeout)
val lock2 = FileLock.for_file(path)
val second = lock2.try_acquire(500)
expect(second).to_equal(false)
lock1.release()
cleanup_lock(path + ".lock")
```

</details>

#### lock can be acquired after previous lock is released

- lock can be acquired after previous lock is released
   - Expected: acquired is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lock can be acquired after previous lock is released")
val path = test_lock_path()
cleanup_lock(path)
cleanup_lock(path + ".lock")
val lock1 = FileLock.for_file(path)
lock1.acquire()
lock1.release()
# After release, new lock should succeed
val lock2 = FileLock.for_file(path)
val acquired = lock2.try_acquire(2000)
expect(acquired).to_equal(true)
lock2.release()
cleanup_lock(path + ".lock")
```

</details>

#### lock file is removed after release

- lock file is removed after release
   - Expected: rt_file_exists(lock_file) is true
   - Expected: rt_file_exists(lock_file) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lock file is removed after release")
val path = test_lock_path()
val lock_file = path + ".lock"
cleanup_lock(path)
cleanup_lock(lock_file)
val lock = FileLock.for_file(path)
lock.acquire()
expect(rt_file_exists(lock_file)).to_equal(true)
lock.release()
expect(rt_file_exists(lock_file)).to_equal(false)
```

</details>

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9d6d6ca26fbaeedf10d1aeaf807c139a052479e78dc7208be640adae7995fb80`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9d6d6ca26fbaeedf10d1aeaf807c139a052479e78dc7208be640adae7995fb80`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9d6d6ca26fbaeedf10d1aeaf807c139a052479e78dc7208be640adae7995fb80`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/stdlib/database/atomic_lock_excl_spec.spl
mirror: doc/06_spec/03_system/stdlib/database/atomic_lock_excl_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/stdlib/database/atomic_lock_excl_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/stdlib/database/atomic_lock_excl_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/stdlib/database/atomic_lock_excl_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates file and returns true when file does not exist' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/stdlib/database/atomic_lock_excl_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns false when file already exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/stdlib/database/atomic_lock_excl_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'writes content to created file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
