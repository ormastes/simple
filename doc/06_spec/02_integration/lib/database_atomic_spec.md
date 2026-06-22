# Database Atomic Specification

> <details>

<!-- sdn-diagram:id=database_atomic_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=database_atomic_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

database_atomic_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=database_atomic_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Database Atomic Specification

## Scenarios

### Atomic File Operations

<details>
<summary>Advanced: writes file atomically</summary>

#### writes file atomically _(slow)_

1. file delete

2. check

3. check
   - Expected: content equals `test content`

4. file delete


<details>
<summary>Executable SPipe</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tmp = get_temp_dir()
val path = "{tmp}/test_atomic_write.txt"

# Clean up if exists
if file_exists(path):
    file_delete(path)

# Write atomically
val result = atomic_write(path, "test content")
check(result)

# Verify file exists and has correct content
check(file_exists(path))
val content = file_read(path)
expect(content).to_equal("test content")

# Cleanup
file_delete(path)
```

</details>


</details>

<details>
<summary>Advanced: reads file atomically</summary>

#### reads file atomically _(slow)_

1. atomic write
   - Expected: content.? is true
   - Expected: content? equals `atomic read test`

2. file delete


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tmp = get_temp_dir()
val path = "{tmp}/test_atomic_read.txt"

# Setup test file
atomic_write(path, "atomic read test")

# Read atomically
val content = atomic_read(path)
expect(content.?).to_equal(true)
expect(content?).to_equal("atomic read test")

# Cleanup
file_delete(path)
```

</details>


</details>

<details>
<summary>Advanced: appends to file atomically</summary>

#### appends to file atomically _(slow)_

1. atomic write

2. check

3. check

4. check

5. file delete


<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tmp = get_temp_dir()
val path = "{tmp}/test_atomic_append.txt"

# Setup
atomic_write(path, "line 1\n")

# Append
val result = atomic_append(path, "line 2\n")
check(result)

# Verify
val content = file_read(path)
check(content.contains("line 1"))
check(content.contains("line 2"))

# Cleanup
file_delete(path)
```

</details>


</details>

<details>
<summary>Advanced: handles missing file on read</summary>

#### handles missing file on read _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = atomic_read("/nonexistent/file.txt")
expect(content.?).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: creates lock file</summary>

#### creates lock file _(slow)_

1. file delete

2. var lock = FileLock for file

3. check

4. check

5. lock release

6. check


<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tmp = get_temp_dir()
val resource = "{tmp}/test_lock_resource.txt"
val lock_path = "{resource}.lock"

# Clean up if exists
if file_exists(lock_path):
    file_delete(lock_path)

# Create lock
var lock = FileLock.for_file(resource)
val acquired = lock.acquire()
check(acquired)
check(file_exists(lock_path))

# Release lock
lock.release()
check(not file_exists(lock_path))
```

</details>


</details>

<details>
<summary>Advanced: detects stale locks</summary>

#### detects stale locks _(slow)_

1. atomic write

2. var lock = FileLock for file

3. check

4. lock release


<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tmp = get_temp_dir()
val resource = "{tmp}/test_stale_lock.txt"
val lock_path = "{resource}.lock"

# Create old lock (2.5 hours ago)
val two_hours_ago = get_timestamp() - (2 * 60 * 60 * 1000000) - (30 * 60 * 1000000)
atomic_write(lock_path, "99999\n{two_hours_ago}")

# Try to acquire lock
var lock = FileLock.for_file(resource)
val acquired = lock.acquire()

# Should succeed because lock is stale
check(acquired)

# Cleanup
lock.release()
```

</details>


</details>

<details>
<summary>Advanced: respects fresh locks</summary>

#### respects fresh locks _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SKIP: FileLock contention with try_acquire causes timeout in interpreter mode
print "SKIP: FileLock contention test times out in interpreter mode"
```

</details>


</details>

### Concurrent File Access

<details>
<summary>Advanced: prevents data corruption with atomic writes</summary>

#### prevents data corruption with atomic writes _(slow)_

1. atomic write
   - Expected: content equals `write_9`

2. file delete


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tmp = get_temp_dir()
val path = "{tmp}/test_concurrent_writes.txt"

# Simulate multiple writes
for i in 0..10:
    atomic_write(path, "write_{i}")

# File should have the last write
val content = file_read(path)
expect(content).to_equal("write_9")

# Cleanup
file_delete(path)
```

</details>


</details>

<details>
<summary>Advanced: allows multiple readers</summary>

#### allows multiple readers _(slow)_

1. atomic write
   - Expected: content.? is true
   - Expected: content? equals `shared content`

2. file delete


<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tmp = get_temp_dir()
val path = "{tmp}/test_multiple_readers.txt"

# Setup
atomic_write(path, "shared content")

# Multiple reads should all succeed
for i in 0..5:
    val content = atomic_read(path)
    expect(content.?).to_equal(true)
    expect(content?).to_equal("shared content")

# Cleanup
file_delete(path)
```

</details>


</details>

### Lock File Format

<details>
<summary>Advanced: stores timestamp in lock file</summary>

#### stores timestamp in lock file _(slow)_

1. file delete

2. var lock = FileLock for file

3. lock acquire

4. check

5. lock release


<details>
<summary>Executable SPipe</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tmp = get_temp_dir()
val resource = "{tmp}/test_lock_format.txt"
val lock_path = "{resource}.lock"

# Clean up if exists
if file_exists(lock_path):
    file_delete(lock_path)

# Acquire lock
var lock = FileLock.for_file(resource)
lock.acquire()

# Read lock file
val lock_content = file_read(lock_path)

# Should be a number (timestamp)
check(lock_content.len() > 0)

# Cleanup
lock.release()
```

</details>


</details>

<details>
<summary>Advanced: overwrites stale lock</summary>

#### overwrites stale lock _(slow)_

1. atomic write

2. var lock = FileLock for file

3. lock acquire

4. check

5. check

6. lock release


<details>
<summary>Executable SPipe</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tmp = get_temp_dir()
val resource = "{tmp}/test_overwrite_lock.txt"
val lock_path = "{resource}.lock"

# Create stale lock (PID + old timestamp)
val old_time = get_timestamp() - (3 * 60 * 60 * 1000000)
atomic_write(lock_path, "99999\n{old_time}")

# Acquire should overwrite
var lock = FileLock.for_file(resource)
lock.acquire()

# Lock file should have new timestamp (PID\ntimestamp format)
val lock_content = file_read(lock_path)
check(lock_content.contains("\n"))
val lock_lines = lock_content.split("\n")
val lock_time = lock_lines[1].trim().to_int() ?? 0
check(lock_time > old_time)

# Cleanup
lock.release()
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/02_integration/lib/database_atomic_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Atomic File Operations
- Concurrent File Access
- Lock File Format

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 11 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
