# Atomic Lock via O_EXCL Specification

> Tests that rt_file_create_excl provides atomic file creation semantics,

<!-- sdn-diagram:id=atomic_lock_excl_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=atomic_lock_excl_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

atomic_lock_excl_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=atomic_lock_excl_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

**ACs:** AC-5 (hardening fix), AC-7 (new tests)
Tests that rt_file_create_excl provides atomic file creation semantics,
and that FileLock.try_create_lock uses it to prevent TOCTOU race conditions.

## Scenarios

### rt_file_create_excl

### basic semantics

#### creates file and returns true when file does not exist

1. cleanup lock
   - Expected: result is true
   - Expected: rt_file_exists(path) is true
2. cleanup lock


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/simple_db_test_excl_create.lock"
cleanup_lock(path)
val result = rt_file_create_excl(path, "pid:12345")
expect(result).to_equal(true)
expect(rt_file_exists(path)).to_equal(true)
cleanup_lock(path)
```

</details>

#### returns false when file already exists

1. cleanup lock
   - Expected: first is true
   - Expected: second is false
2. cleanup lock


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. cleanup lock
2. rt file create excl
   - Expected: rt_file_exists(path) is true
3. cleanup lock


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/simple_db_test_excl_content.lock"
cleanup_lock(path)
rt_file_create_excl(path, "test_content_here")
expect(rt_file_exists(path)).to_equal(true)
cleanup_lock(path)
```

</details>

### edge cases

#### handles empty content

1. cleanup lock
   - Expected: result is true
2. cleanup lock


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/simple_db_test_excl_empty.lock"
cleanup_lock(path)
val result = rt_file_create_excl(path, "")
expect(result).to_equal(true)
cleanup_lock(path)
```

</details>

#### returns false for invalid directory path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = rt_file_create_excl("/nonexistent_dir_abc/test.lock", "x")
expect(result).to_equal(false)
```

</details>

### FileLock with O_EXCL

#### sequential lock on same path: first succeeds, second fails

1. cleanup lock
2. cleanup lock
   - Expected: acquired is true
   - Expected: second is false
3. lock1 release
4. cleanup lock


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. cleanup lock
2. cleanup lock
3. lock1 acquire
4. lock1 release
   - Expected: acquired is true
5. lock2 release
6. cleanup lock


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. cleanup lock
2. cleanup lock
3. lock acquire
   - Expected: rt_file_exists(lock_file) is true
4. lock release
   - Expected: rt_file_exists(lock_file) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
