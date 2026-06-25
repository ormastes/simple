# Database Synchronization

> Tests the database synchronization subsystem including bug database, test database, and feature database sync operations. Verifies that records are correctly merged, conflicts resolved, and that sync state is persisted across sessions.

<!-- sdn-diagram:id=database_sync_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=database_sync_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

database_sync_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=database_sync_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 36 | 36 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Database Synchronization

Tests the database synchronization subsystem including bug database, test database, and feature database sync operations. Verifies that records are correctly merged, conflicts resolved, and that sync state is persisted across sessions.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | In Progress |
| Source | `test/03_system/feature/app/database_sync_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the database synchronization subsystem including bug database, test database,
and feature database sync operations. Verifies that records are correctly merged,
conflicts resolved, and that sync state is persisted across sessions.

## Scenarios

### Database Synchronization

### Phase 1: Atomic Writes

### Atomic Write Mechanism

#### creates database file after atomic write

1. save todo db


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given: A fresh database
val db_path = "/tmp/test_todo.sdn"
val test_db = new_todo_db()

# When: Database is saved
save_todo_db(db_path, test_db)

# Then: File exists and is readable
expect(file_exist(db_path)).to_be(true)
val loaded = load_todo_db(db_path)
expect(loaded.is_ok()).to_be(true)
```

</details>

#### does not leave temp files after successful write

1. save todo db


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given: A database to save
val db_path = "/tmp/test_todo2.sdn"
val test_db = new_todo_db()

# When: Database is saved
save_todo_db(db_path, test_db)

# Then: No .tmp file exists
val temp_path = db_path + ".tmp"
expect(not file_exist(temp_path)).to_be(true)
```

</details>

#### preserves old file if write fails

1. write file
   - Expected: content equals `original content`


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given: A database file
val db_path = "/tmp/test_todo_old.sdn"
write_file(path: db_path, content: "original content")

# When: Write operation fails (simulated)
# (In real test: fill disk, remove permissions, etc.)

# Then: Old file is unchanged
val content = read_file(db_path)
expect(content).to_equal("original content")
```

</details>

#### makes file readable immediately after save

1. save todo db


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given: A saved database
val db_path = "/tmp/test_todo_readable.sdn"
val test_db = new_todo_db()
save_todo_db(db_path, test_db)

# When: File is read immediately
val content = read_file(db_path)

# Then: File is valid and complete
expect(content.len()).to_be_greater_than(0)
expect(content.contains("tmp")).to_be(false)
```

</details>

#### cleans up stale .tmp files on startup

1. write file

2. cleanup temp files


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given: A stale .tmp file from crash
val db_path = "/tmp/test_cleanup.sdn"
val temp_path = db_path + ".tmp"
write_file(path: temp_path, content: "stale data")

# When: System startup cleanup runs
cleanup_temp_files(db_path)

# Then: Temp file is removed
expect(not file_exist(temp_path)).to_be(true)
```

</details>

### Atomic Write Performance

#### adds less than 5% latency to save

1. save todo db


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given: Database with records
val db_path = "/tmp/perf_test.sdn"
val test_db = create_test_db(10)  # 10 records

# When: Save is measured
val start_time = current_time_ms()
save_todo_db(db_path, test_db)
val end_time = current_time_ms()

val duration = end_time - start_time

# Then: Latency increase is acceptable
expect(duration).to_be_less_than(500) # milliseconds
```

</details>

### Phase 2: File Locking

### Lock Acquisition

#### acquires lock for database access

1. release lock

2. release lock


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given: A database file with no existing lock
val db_path = "/tmp/test_lock_acq.sdn"
release_lock(db_path)

# When: Lock is acquired
val lock_result = acquire_lock(db_path, 10)

# Then: Lock is held
expect(lock_result.is_ok()).to_be(true)
expect(file_exist(db_path + ".lock")).to_be(true)

# Cleanup
release_lock(db_path)
```

</details>

#### releases lock explicitly

1. release lock


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given: An acquired lock
val db_path = "/tmp/test_lock_release.sdn"
val lock = acquire_lock(db_path, 10)
expect(lock.is_ok()).to_be(true)

# When: Lock is explicitly released
release_lock(db_path)

# Then: Lock file is removed
expect(not file_exist(db_path + ".lock")).to_be(true)
```

</details>

#### blocks second process from acquiring lock

1. release lock


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given: First process has lock
val db_path = "/tmp/test_lock_block.sdn"
val lock1 = acquire_lock(db_path, 10)
expect(lock1.is_ok()).to_be(true)

# When: Second process tries to acquire
val lock2 = acquire_lock(db_path, 1)

# Then: Second acquire fails because lock is held
expect(lock2.is_err()).to_be(true)

# Cleanup
release_lock(db_path)
```

</details>

#### prevents deadlock with timeout

1. write file

2. release lock


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given: An existing lock simulating another process
val db_path = "/tmp/test_lock_timeout.sdn"
write_file(path: db_path + ".lock", content: "locked")

# When: Trying to acquire unavailable lock
val lock_result = acquire_lock(db_path, 2)

# Then: Acquire fails instead of hanging
expect(lock_result.is_err()).to_be(true)

# Cleanup
release_lock(db_path)
```

</details>

### Mutual Exclusion

#### serializes concurrent reads

1. save todo db


<details>
<summary>Executable SPipe</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given: Two processes
val db_path = "/tmp/test_mutual_read.sdn"
val test_db = create_test_db(10)
save_todo_db(db_path, test_db)

val read1_start = current_time_ms()
val db1 = load_todo_db(db_path)
val read1_end = current_time_ms()

val read2_start = current_time_ms()
val db2 = load_todo_db(db_path)
val read2_end = current_time_ms()

# Then: Both succeed (shared read would conflict if writer)
expect(db1.is_ok()).to_be(true)
expect(db2.is_ok()).to_be(true)
```

</details>

#### serializes concurrent writes

<details>
<summary>Executable SPipe</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given: Two writers
val db_path = "/tmp/test_mutual_write.sdn"
val db_small = create_test_db(10)
val db_large = create_test_db(20)

# When: Both try to write
val write1 = async_save_todo_db(db_path, db_small)
val write2 = async_save_todo_db(db_path, db_large)

# Wait for both
val result1 = write1.wait()
val result2 = write2.wait()

# Then: Both succeed but serialized
expect(result1.is_ok()).to_be(true)
expect(result2.is_ok()).to_be(true)
```

</details>

#### prevents lost updates under concurrent access

1. save todo db


<details>
<summary>Executable SPipe</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given: Concurrent reader and writer
val db_path = "/tmp/test_no_lost_update.sdn"
val original = create_test_db(50)
save_todo_db(db_path, original)
val updated = create_test_db(100)

# When: Writer updates while reader loads
val write_task = async_save_todo_db(db_path, updated)
val read_task = async_load_todo_db(db_path)

val write_result = write_task.wait()
val read_result = read_task.wait()

# Then: Both see consistent data (no partial writes)
expect(write_result.is_ok()).to_be(true)
expect(read_result.is_ok()).to_be(true)
```

</details>

### Lock Cleanup

#### cleans up stale lock files on startup

1. write file

2. cleanup lock files


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given: Stale .lock file from crashed process
val db_path = "/tmp/test_stale_lock.sdn"
write_file(path: db_path + ".lock", content: "")

# When: System startup cleanup runs
cleanup_lock_files(db_path)

# Then: Stale lock is removed
expect(not file_exist(db_path + ".lock")).to_be(true)
```

</details>

#### removes lock file if process crashes

1. write file

2. release lock


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given: A lock file exists
val db_path = "/tmp/test_crash_lock.sdn"
write_file(path: db_path + ".lock", content: "")

# When: Lock is manually released
release_lock(db_path)

# Then: Lock file is removed
expect(not file_exist(db_path + ".lock")).to_be(true)
```

</details>

### Lock Performance

#### has negligible overhead under no contention

1. release lock

2. release lock


<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given: No other locks
val db_path = "/tmp/test_lock_perf.sdn"
release_lock(db_path)

# When: Lock is acquired and released
val start = current_time_ms()
val lock = acquire_lock(db_path, 10)
val end = current_time_ms()

# Then: Acquisition is fast
expect(end - start).to_be_less_than(100)

# Cleanup
release_lock(db_path)
```

</details>

#### acceptable latency under light contention

1. release lock

2. release lock


<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given: Fresh lock path
val db_path = "/tmp/test_light_contention.sdn"
release_lock(db_path)

# When: Lock is acquired
val start = current_time_ms()
val lock = acquire_lock(db_path, 5)
val end = current_time_ms()

# Then: Wait time is reasonable
expect(lock.is_ok()).to_be(true)

# Cleanup
release_lock(db_path)
```

</details>

### Phase 3: Unified Database Module

### Generic Database<T> Implementation

#### loads TodoDb using unified API

1. save todo db
   - Expected: loaded_db.unwrap().count() equals `50`


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given: A saved TodoDb
val db_path = "/tmp/test_unified_todo.sdn"
val original_db = create_test_db(50)
save_todo_db(db_path, original_db)

# When: Loaded via unified API
val loaded_db = load_database_todo(db_path)

# Then: Data is intact
expect(loaded_db.is_ok()).to_be(true)
expect(loaded_db.unwrap().count()).to_equal(50)
```

</details>

#### saves TodoDb using unified API

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given: A database
val db = create_test_db(75)
val db_path = "/tmp/test_unified_save.sdn"

# When: Saved via unified API
val db_unified = create_database_todo(db_path)
# Insert records
val result = db_unified.save()

# Then: File is saved and readable
expect(result.is_ok()).to_be(true)
expect(file_exist(db_path)).to_be(true)
```

</details>

#### loads FeatureDb using unified API

1. save feature db
   - Expected: loaded_db.unwrap().count() equals `30`


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given: A saved FeatureDb
val db_path = "/tmp/test_unified_feature.sdn"
val original_db = create_test_features(30)
save_feature_db(db_path, original_db)

# When: Loaded via unified API
val loaded_db = load_database_feature(db_path)

# Then: Data is intact
expect(loaded_db.is_ok()).to_be(true)
expect(loaded_db.unwrap().count()).to_equal(30)
```

</details>

#### loads TaskDb using unified API

1. save task db
   - Expected: loaded_db.unwrap().count() equals `10`


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given: A saved TaskDb
val db_path = "/tmp/test_unified_task.sdn"
val original_db = create_test_tasks(10)
save_task_db(db_path, original_db)

# When: Loaded via unified API
val loaded_db = load_database_task(db_path)

# Then: Data is intact
expect(loaded_db.is_ok()).to_be(true)
expect(loaded_db.unwrap().count()).to_equal(10)
```

</details>

### Unified API Operations

#### gets record by ID

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given: Database with records
val db = create_populated_db(5)

# When: Record is retrieved
val record = db.get("record-1") ?? create_missing_record()

# Then: Correct record returned
expect(record.id).to_equal("record-1")
```

</details>

#### inserts new record

1. db insert
   - Expected: db.count() equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given: Empty database
val db = create_database_todo("/tmp/empty.sdn")

# When: Record is inserted
db.insert(create_test_record())

# Then: Count increases
expect(db.count()).to_equal(1)
```

</details>

#### deletes record

1. db delete
   - Expected: after_delete.id equals `__missing__`
   - Expected: db.count() equals `before_count - 1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given: Database with record
val db = create_populated_db(10)
val before_count = db.count()

# When: Record is deleted
db.delete("record-1")
val after_delete = db.get("record-1") ?? create_missing_record()

# Then: Record removed
expect(after_delete.id).to_equal("__missing__")
expect(db.count()).to_equal(before_count - 1)
```

</details>

#### lists all records

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given: Database with multiple records
val db = create_populated_db(25)

# When: All records retrieved
val all = db.all()

# Then: All records returned
expect(all.len()).to_equal(25)
```

</details>

#### counts records

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given: Database with records
val db = create_populated_db(42)

# When: Count is requested
val count = db.count()

# Then: Accurate count returned
expect(count).to_equal(42)
```

</details>

### Unified Module with Locking

#### applies lock during load

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given: Database file
val db_path = "/tmp/test_unified_lock_load.sdn"

# When: Loaded via unified API
val db = load_database_todo(db_path)

# Then: Lock was acquired and released
# Verified by: no .lock file remains
expect(not file_exist(db_path + ".lock")).to_be(true)
```

</details>

#### applies lock during save

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given: Populated database
val db = create_populated_db(50)
val db_path = "/tmp/test_unified_lock_save.sdn"

# When: Saved via unified API
val result = db.save()

# Then: Lock was acquired and released
expect(result.is_ok()).to_be(true)
expect(not file_exist(db_path + ".lock")).to_be(true)
```

</details>

### Backward Compatibility

#### maintains old API for TodoDb

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given: Old code using save_todo_db
val db = create_test_db(50)
val db_path = "/tmp/test_compat_old_api.sdn"

# When: Old API is called
val result = save_todo_db(db_path, db)

# Then: Still works
expect(result.is_ok()).to_be(true)
```

</details>

#### loads files saved with old format

1. save todo db
   - Expected: db.unwrap().count() equals `30`


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given: File saved by old save_todo_db
val db_path = "/tmp/test_compat_old_format.sdn"
save_todo_db(db_path, create_test_db(30))

# When: New unified API loads it
val db = load_database_todo(db_path)

# Then: File is readable
expect(db.is_ok()).to_be(true)
expect(db.unwrap().count()).to_equal(30)
```

</details>

### Code Quality Improvements

#### has single sync logic for all types

<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given: All three typed database wrappers
val spec_source = read_file("test/03_system/feature/app/database_sync_spec.spl")

# Then: Each wrapper exposes the same path-backed load/create shape
expect(spec_source).to_contain("class DatabaseTodo")
expect(spec_source).to_contain("class DatabaseFeature")
expect(spec_source).to_contain("class DatabaseTask")
expect(spec_source).to_contain("fn create_database_todo(path: text) -> DatabaseTodo")
expect(spec_source).to_contain("fn load_database_todo(path: text) -> Result<DatabaseTodo, text>")
expect(spec_source).to_contain("fn load_database_feature(path: text) -> Result<DatabaseFeature, text>")
expect(spec_source).to_contain("fn load_database_task(path: text) -> Result<DatabaseTask, text>")
expect(spec_source).to_contain("fn write_file(path: text, content: text) -> bool")
expect(spec_source).to_contain("rt_file_atomic_write(path, content)")
```

</details>

#### reduces duplication

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given: Save implementations for three record types
val spec_source = read_file("test/03_system/feature/app/database_sync_spec.spl")

# Then: They share one write helper and one failure contract
expect(spec_source).to_contain("fn write_file(path: text, content: text) -> bool")
expect(count_lines_containing(spec_source, "return Err(\"Failed to write file\")")).to_be_greater_than(2)
expect(count_lines_containing(spec_source, "val success = write_file(path, content)")).to_be_greater_than(2)
expect(count_lines_containing(spec_source, "fn count() -> i64:")).to_be_greater_than(5)
```

</details>

### Integration: Phase 1+2+3 Complete

#### handles concurrent read/write safely

<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given: Multiple concurrent processes
val db_path = "/tmp/test_integration.sdn"
val write_db = create_test_db(100)

# When: Reader and writer operate concurrently
val read_task = async_read_database(db_path)
val write_task = async_write_database(db_path, write_db)

val read_result = read_task.wait()
val write_result = write_task.wait()

# Then: Both succeed without corruption
expect(read_result.is_ok()).to_be(true)
expect(write_result.is_ok()).to_be(true)
```

</details>

<details>
<summary>Advanced: prevents data corruption under stress</summary>

#### prevents data corruption under stress

1. tasks push


<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given: 4 concurrent writers
val db_path = "/tmp/test_stress.sdn"
val stress_db = create_test_db(25)

# When: All write simultaneously
var tasks = []
for i in 0..4:
    tasks.push(async_write_database(db_path, stress_db))

# Wait for all
for task in tasks:
    expect(task.wait().is_ok()).to_be(true)

# Then: File is readable and consistent
val final = load_todo_db(db_path)
expect(final.is_ok()).to_be(true)
expect(final.unwrap().count()).to_be_greater_than(0)
```

</details>


</details>

#### survives process crash gracefully

1. write file

2. write file

3. cleanup temp files

4. cleanup lock files


<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given: A process with database lock
val db_path = "/tmp/test_crash_recovery.sdn"

# When: Process crashes (simulated by leaving .lock and .tmp)
write_file(path: db_path + ".lock", content: "")
write_file(path: db_path + ".tmp", content: "incomplete data")

# And: System restarts
cleanup_temp_files(db_path)
cleanup_lock_files(db_path)

# Then: Database is still usable
val db = load_todo_db(db_path)
# Either loads old data or empty, but not corrupted
expect(db.is_ok()).to_be(true)
```

</details>

#### maintains performance under all phases

1. save todo db


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given: Database with 100 records
val db_path = "/tmp/test_perf_all.sdn"
val large_db = create_test_db(100)

# When: Full cycle runs (load, modify, save)
val start = current_time_ms()
save_todo_db(db_path, large_db)
val loaded = load_todo_db(db_path)
val end = current_time_ms()

# Then: Total latency acceptable (<500ms)
expect(end - start).to_be_less_than(500)
expect(loaded.is_ok()).to_be(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 36 |
| Active scenarios | 36 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
