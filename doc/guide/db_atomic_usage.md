# Atomic Text Database Library - Usage Guide

## Overview

The `std.db_atomic` module provides thread-safe, atomic database operations for SDN-formatted text files. It combines file locking, atomic writes, and backup management into a unified API.

## Key Features

✅ **Thread-Safe**: File locking prevents concurrent modification
✅ **Atomic Writes**: Write-temp-rename pattern ensures consistency
✅ **Automatic Backups**: Rotating backup system with configurable retention
✅ **Size Limits**: Prevents unbounded file growth
✅ **Read-Modify-Write**: Transaction-like updates with locking

## Quick Start

### 1. Basic Read/Write

```simple
use std.db_atomic.{atomic_read, atomic_write, DbConfig}

# Read file atomically
val content = atomic_read("data.sdn", DbConfig.defaults())?

# Write file atomically
atomic_write("data.sdn", "new content", DbConfig.defaults())?
```

### 2. Atomic Updates

```simple
use std.db_atomic.{atomic_update, DbConfig}

# Append a row atomically
val result = atomic_update("data.sdn", |content| {
    content + "\n    new_row, value1, value2"
}, DbConfig.defaults())

match result:
    case Ok(_): print "Updated successfully"
    case Err(e): print "Error: {e}"
```

### 3. Using AtomicTable

```simple
use std.db_atomic.{AtomicTable, DbConfig}

# Create new table
val config = DbConfig.defaults()
val table = AtomicTable.create(
    "todos.sdn",
    "todos",
    ["id", "title", "status"],
    config
)?

# Add row
table.add_row(["1", "Fix bug", "done"])?

# Load existing table
val existing = AtomicTable.load("todos.sdn", "todos", config)?
```

## Configuration Profiles

### Default (Recommended)
```simple
val config = DbConfig.defaults()
# - 10 second lock timeout
# - 500 MB size limit
# - Backups enabled (5 kept)
# - No debug logging
```

### No Backups (Faster)
```simple
val config = DbConfig.no_backups()
# - Same as defaults but no backup creation
# - Use for temporary/cache files
```

### Strict (Maximum Safety)
```simple
val config = DbConfig.strict()
# - 30 second lock timeout
# - 100 MB size limit
# - Backups enabled (10 kept)
# - Debug logging enabled
```

### Custom
```simple
val config = DbConfig(
    lock_timeout_secs: 5,
    max_file_size_mb: 50,
    create_backups: true,
    backup_count: 3,
    enable_logging: false
)
```

## Architecture

### Components

```
┌─────────────────────┐
│  AtomicTable API    │  High-level table operations
├─────────────────────┤
│  atomic_read/write  │  Mid-level file operations
├─────────────────────┤
│  FileLock           │  OS-level file locking
├─────────────────────┤
│  file_atomic_write  │  SFFI wrapper (write-temp-rename)
└─────────────────────┘
```

### Atomic Write Pattern

```
1. Acquire exclusive file lock
2. Create backup (if configured)
3. Write to temporary file
4. Rename temp → target (atomic)
5. Release lock
```

### Backup Rotation

```
data.sdn         ← Current file
data.sdn.bak     ← Most recent backup
data.sdn.bak.1   ← Previous backup
data.sdn.bak.2   ← Older backup
...
data.sdn.bak.N   ← Oldest backup (N = backup_count)
```

## Error Handling

All operations return `Result<T, text>`:

```simple
match atomic_write(path, content, config):
    case Ok(_):
        print "Success"
    case Err("Failed to acquire lock"):
        print "Another process holds the lock"
    case Err("File exceeds size limit"):
        print "File too large"
    case Err(msg):
        print "Unknown error: {msg}"
```

## Common Patterns

### Append-Only Log
```simple
fn log_entry(path: text, entry: text) -> Result<(), text>:
    atomic_update(path, |content| {
        val timestamp = time_now_iso()
        content + "\n[{timestamp}] {entry}"
    }, DbConfig.defaults())
```

### Counter Increment
```simple
fn increment_counter(path: text) -> Result<i64, text>:
    var new_value = 0

    val result = atomic_update(path, |content| {
        val current = content.trim().parse_int() ?? 0
        new_value = current + 1
        "{new_value}"
    }, DbConfig.defaults())

    if result.ok.?:
        Ok(new_value)
    else:
        Err(result.unwrap_err())
```

### Conditional Update
```simple
fn update_if_matches(path: text, expected: text, new: text) -> Result<bool, text>:
    var matched = false

    val result = atomic_update(path, |content| {
        if content.trim() == expected:
            matched = true
            new
        else:
            content  # No change
    }, DbConfig.defaults())

    if result.ok.?:
        Ok(matched)
    else:
        Err(result.unwrap_err())
```

## Migration from Existing Code

### From Direct FFI Calls

**Before:**
```simple
use app.io.mod (file_read, file_write)

val content = file_read("data.sdn")
file_write("data.sdn", new_content)
```

**After:**
```simple
use std.db_atomic.{atomic_read, atomic_write, DbConfig}

val content = atomic_read("data.sdn", DbConfig.defaults())?
atomic_write("data.sdn", new_content, DbConfig.defaults())?
```

### From test_db_io.spl

**Before:**
```simple
use test_db_io.{read_db_file, write_db_file_locked}

val content = read_db_file("test_db.sdn")?
write_db_file_locked("test_db.sdn", new_content)?
```

**After:**
```simple
use std.db_atomic.{atomic_read, atomic_write, DbConfig}

val content = atomic_read("test_db.sdn", DbConfig.defaults())?
atomic_write("test_db.sdn", new_content, DbConfig.defaults())?
```

### From std.src.db.spl

**Before:**
```simple
use std.src.db.Table

val table = Table.load("data.sdn", "todos")
table.add_row(["1", "title", "status"])
table.save()
```

**After:**
```simple
use std.db_atomic.{AtomicTable, DbConfig}

val table = AtomicTable.load("data.sdn", "todos", DbConfig.defaults())?
table.add_row(["1", "title", "status"])?
# Auto-saved atomically
```

## Performance Considerations

### Locking Overhead
- File locks add ~1-5ms per operation
- Acceptable for most use cases
- Avoid in hot loops (batch updates instead)

### Backup Overhead
- Backup creation: ~2-10ms for small files (<1MB)
- Scales linearly with file size
- Disable for temporary files: `DbConfig.no_backups()`

### Size Limits
- Default 500MB limit protects against runaway growth
- Reading large files can cause memory pressure
- Consider splitting large databases

### Batch Operations

**Bad (multiple locks):**
```simple
for item in items:
    table.add_row(item)?  # Lock acquired N times
```

**Good (single lock):**
```simple
table.update(|content| {
    var new_content = content
    for item in items:
        new_content = new_content + format_row(item)
    new_content
})?  # Lock acquired once
```

## Troubleshooting

### Lock Timeout
**Symptom**: `Failed to acquire lock (timeout: 10s)`
**Cause**: Another process holds the lock too long
**Fix**: Increase timeout or check for deadlocks

### Size Limit Exceeded
**Symptom**: `File exceeds size limit (550 MB > 500 MB)`
**Cause**: File grew beyond configured limit
**Fix**: Increase limit or archive old data

### Empty Overwrites
**Symptom**: `Safety: refusing to overwrite non-empty with empty content`
**Cause**: Attempted to write empty string to non-empty file
**Fix**: This is intentional - prevents data loss. Check your logic.

## Best Practices

✅ **Always use Result types**: Check for errors, don't ignore them
✅ **Configure per use-case**: Use strict config for critical data
✅ **Batch updates**: Minimize lock acquisitions
✅ **Keep files small**: Split large databases
✅ **Monitor backups**: Clean up old backups periodically
✅ **Test recovery**: Verify backups work

❌ **Don't hold locks long**: Quick operations only
❌ **Don't nest locks**: Risk of deadlock
❌ **Don't ignore size limits**: Monitor file growth
❌ **Don't disable backups for important data**: Safety first

## Testing

```simple
use std.db_atomic.{atomic_write, atomic_read, DbConfig}

fn test_atomic_operations():
    val config = DbConfig.defaults()
    val test_file = "/tmp/test_atomic.sdn"

    # Write
    val write_result = atomic_write(test_file, "test content", config)
    assert(write_result.ok.?)

    # Read
    val read_result = atomic_read(test_file, config)
    assert(read_result.ok.?)
    assert(read_result.unwrap() == "test content")

    # Update
    val update_result = atomic_update(test_file, |c| c + " updated", config)
    assert(update_result.ok.?)

    # Verify
    val content = atomic_read(test_file, config).unwrap()
    assert(content == "test content updated")
```

## Related

- **`std.atomic`** - Low-level atomic primitives (AtomicI64, etc.)
- **`std.src.db`** - Basic database (NOT thread-safe)
- **`app.io.mod`** - File I/O wrappers (SFFI)
- **Test Database** - Example usage: `src/app/test_runner_new/test_db_core.spl`

## Future Enhancements

🚧 **Planned:**
- Transaction support (begin/commit/rollback)
- Multi-table operations
- Index support for faster lookups
- Compression for large files
- Network locking (distributed systems)
- Optimistic concurrency control

## See Also

- **Implementation**: `src/std/db_atomic.spl`
- **Tests**: `test/std/db_atomic_spec.spl` (TODO)
- **Examples**: `example/db_atomic_example.spl` (TODO)
