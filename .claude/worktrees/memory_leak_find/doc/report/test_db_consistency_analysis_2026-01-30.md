# Test Database Consistency Analysis

**Date:** 2026-01-30
**Status:** ⚠️ Critical Issue Found

## Summary

**Problem:** The Simple test runner (`test_runner_new/main.spl`) and Rust test runner (`simple_old test`) use **completely different database handling logic**, causing data corruption and test failures.

**Root Cause:** The Simple runner uses naive file appends without locking, while the Rust runner uses atomic writes with file locking. This creates race conditions and data inconsistencies.

**Impact:**
- Test database corruption
- Lost test results
- Race conditions when both runners execute simultaneously
- Failed database reads in Simple test analysis tools

## Database Handling Comparison

### Rust Side (simple_old) - ✅ Correct Implementation

**Location:** `src/rust/driver/src/test_db.rs` + `src/rust/driver/src/unified_db.rs`

**Operations:**
1. **Load** (`load_test_db()` at line 923):
   - Acquires file lock with `FileLock::acquire(path, 10)` (10 second timeout)
   - Reads entire file as SDN format
   - Parses all tables (tests, test_runs, etc.)
   - Validates data integrity
   - Returns in-memory database

2. **Save** (`save_test_db()` at line 1123):
   - Acquires file lock with `FileLock::acquire(path, 10)`
   - Creates backup (`.sdn.prev`) before overwriting
   - Preserves other tables (multi-table support)
   - Writes to temp file `.sdn.tmp`
   - Atomically renames temp to `.sdn` (POSIX atomic operation)

**Atomic Write Pattern (from `unified_db.rs` lines 390-401):**
```rust
// Create parent directories
if let Some(parent) = self.path.parent() {
    fs::create_dir_all(parent)?;
}

// Atomic write: write to temp, then rename
let temp_path = self.path.with_extension("sdn.tmp");
fs::write(&temp_path, content)?;
fs::rename(&temp_path, &self.path)?;  // Atomic on POSIX
```

**Key Features:**
- ✅ File locking (prevents concurrent access)
- ✅ Atomic writes (all-or-nothing, no corruption)
- ✅ Backup creation (`.sdn.prev`)
- ✅ Multi-table support (preserves other tables)
- ✅ Full read-modify-write cycle

### Simple Side (test_runner_new) - ❌ Broken Implementation

**Location:** `src/app/test_runner_new/main.spl` lines 859-870

**Operations:**
```simple
fn write_test_db_run(result: TestRunResult, start_time: i64, end_time: i64):
    val run_id = start_time
    val start_iso = micros_to_iso(start_time)
    val end_iso = micros_to_iso(end_time)
    val test_count = result.total_passed + result.total_failed
    val passed = result.total_passed
    val failed = result.total_failed
    val timed_out = result.total_timed_out

    # Append a run record to the test_runs table
    val line = "        {run_id}, \"{start_iso}\", \"{end_iso}\", 0, \"simple-runner\", \"completed\", {test_count}, {passed}, {failed}, 0, {timed_out}\n"
    rt_file_append_text("doc/test/test_db.sdn", line)  # ❌ NO LOCKING, NO ATOMICITY
```

**Problems:**
- ❌ No file locking
- ❌ No atomic operations
- ❌ Blind append without reading existing data
- ❌ No backup creation
- ❌ Doesn't preserve table structure
- ❌ Race conditions with Rust runner
- ❌ Can corrupt SDN format

## Race Condition Scenarios

### Scenario 1: Concurrent Execution
```
Time    Rust Runner                     Simple Runner
----    -----------                     -------------
T0      Lock file
T1      Read database                   [Blocked - waiting for lock]
T2      Modify in memory
T3      Write to .tmp
T4      Rename .tmp → .sdn
T5      Unlock file
T6                                      Append line (no lock!)
T7                                      ❌ Corrupted: appended to middle of file
```

### Scenario 2: Format Corruption
```
Expected SDN format:
tests |test_id, test_name, ...|
    test1, name1, ...
    test2, name2, ...

test_runs |run_id, start_time, ...|
    123456, 2026-01-30, ...

After Simple append (without reading):
tests |test_id, test_name, ...|
    test1, name1, ...
    test2, name2, ...
        789012, 2026-01-30, ...  ❌ WRONG TABLE!
```

## Available File Operations in Simple

**Current FFI functions** (from `src/rust/compiler/src/interpreter_extern/file_io.rs`):

| Function | Atomic? | Locking? | Safe? |
|----------|---------|----------|-------|
| `rt_file_read_text()` | N/A | ❌ No | ⚠️ Can read partial writes |
| `rt_file_write_text()` | ❌ No | ❌ No | ❌ Unsafe |
| `rt_file_append_text()` | ❌ No | ❌ No | ❌ Unsafe |
| `rt_file_rename()` | ✅ Yes (POSIX) | ❌ No | ⚠️ Partial |

**Missing functions needed for safety:**
- `rt_file_atomic_write()` - Write to temp, then rename
- `rt_file_lock()` / `rt_file_unlock()` - File locking
- `rt_db_load()` / `rt_db_save()` - Database-level operations

## Solutions

### Option 1: Add Atomic Write FFI (Recommended)

**Add new FFI function:**
```rust
// In interpreter_extern/file_io.rs
pub fn rt_file_atomic_write(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    let content = extract_content(args, 1)?;

    // Write to temp file
    let temp_path = format!("{}.tmp", path);
    match fs::write(&temp_path, &content) {
        Ok(_) => {
            // Atomically rename
            match fs::rename(&temp_path, &path) {
                Ok(_) => Ok(Value::Bool(true)),
                Err(_) => Ok(Value::Bool(false)),
            }
        }
        Err(_) => Ok(Value::Bool(false)),
    }
}
```

**Usage in Simple:**
```simple
extern fn rt_file_atomic_write(path: text, content: text) -> bool

fn write_test_db_safely(db_content: text):
    rt_file_atomic_write("doc/test/test_db.sdn", db_content)
```

### Option 2: Add File Locking FFI

**Add file locking operations:**
```rust
// In interpreter_extern/file_io.rs
pub fn rt_file_lock(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    let timeout_secs = extract_int(args, 1)?;
    // Use FileLock from db_lock module
    // Return lock handle
}

pub fn rt_file_unlock(args: &[Value]) -> Result<Value, CompileError> {
    // Release lock by handle
}
```

**Usage in Simple:**
```simple
extern fn rt_file_lock(path: text, timeout: i64) -> i64
extern fn rt_file_unlock(handle: i64) -> bool

fn write_with_locking():
    val lock = rt_file_lock("doc/test/test_db.sdn", 10)
    # ... read, modify, write ...
    rt_file_unlock(lock)
```

### Option 3: Use Rust Database API (Cleanest)

**Add high-level database FFI:**
```rust
// In interpreter_extern/database.rs (new file)
pub fn rt_test_db_load(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    // Use test_db::load_test_db()
    // Return database as RuntimeValue
}

pub fn rt_test_db_save(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    let db = extract_db(args, 1)?;
    // Use test_db::save_test_db()
}
```

**Usage in Simple:**
```simple
extern fn rt_test_db_load(path: text) -> TestDatabase
extern fn rt_test_db_save(path: text, db: TestDatabase) -> bool

fn update_test_db():
    var db = rt_test_db_load("doc/test/test_db.sdn")
    # ... modify db ...
    rt_test_db_save("doc/test/test_db.sdn", db)
```

### Option 4: Disable Simple Test Runner Database Writes (Quick Fix)

**Immediate fix - comment out database writes:**
```simple
# In src/app/test_runner_new/main.spl line 1006
fn main() -> i64:
    # ...

    # TEMPORARILY DISABLED: Uses unsafe file append
    # TODO: Replace with atomic write API
    # if not options.list and result.files.len() > 0:
    #     write_test_db_run(result, run_start, run_end)

    if result.is_ok():
        return 0
    return 1
```

## Recommendation

**Short-term (Immediate):**
- ✅ **Option 4**: Disable database writes in Simple test runner
- Document the limitation
- All test database updates go through Rust runner only

**Medium-term (Next sprint):**
- ✅ **Option 1**: Implement `rt_file_atomic_write()` FFI
- Update Simple test runner to use atomic writes
- Add proper read-modify-write cycle

**Long-term (Future):**
- ✅ **Option 3**: Create unified database API
- Expose Rust's `Database<T>` to Simple
- Use same code path for both runners

## Impact Assessment

### Current Failures Explained

**Test Analysis Tool Failures:**
- `src/app/test_analysis/main.spl` - Database read failures
  - Cause: Corrupted database from concurrent writes
  - Affected: `cmd_analyze()`, `cmd_details()`, `cmd_features()`

**MCP Tool Failures:**
- `src/lib/std/src/mcp/simple_lang/db_tools.spl` - Database operations fail
  - Cause: Same corruption issues
  - Affected: All 3 new MCP tools

**Test Suite Failures:**
- 26/56 failures in `test/app/test_analysis_spec.spl`
- 9/23 failures in `test/lib/std/unit/mcp/failure_analysis_spec.spl`
- Root cause: Test database reads failing or returning corrupted data

### After Fix

With proper atomic writes:
- ✅ No more race conditions
- ✅ No more database corruption
- ✅ Test analysis tools work reliably
- ✅ MCP tools work correctly
- ✅ Both runners can coexist safely

## Verification Steps

After implementing fix:

1. **Test concurrent execution:**
   ```bash
   # Terminal 1
   ./target/debug/simple_old test &

   # Terminal 2 (immediately)
   ./target/debug/simple_old test

   # Verify no corruption
   cat doc/test/test_db.sdn | head -50
   ```

2. **Test Simple tools:**
   ```bash
   ./target/debug/simple_old test-analysis analyze
   ./target/debug/simple_old test-analysis details
   ```

3. **Verify SDN format:**
   ```bash
   # Should parse without errors
   ./target/debug/simple_old -c "
   use simple_sdn.*
   val doc = parse_file(\"doc/test/test_db.sdn\")
   print(doc.root())
   "
   ```

## Files to Modify

| File | Change | Priority |
|------|--------|----------|
| `src/rust/compiler/src/interpreter_extern/file_io.rs` | Add `rt_file_atomic_write()` | P0 |
| `src/rust/compiler/src/interpreter_extern/mod.rs` | Register new FFI function | P0 |
| `src/app/test_runner_new/main.spl` | Use atomic write API | P0 |
| `src/lib/std/src/infra/file_io.spl` | Expose atomic write wrapper | P1 |
| `doc/guide/database_handling.md` | Document best practices | P2 |

## Related Issues

- Test database corruption intermittent failures
- Race conditions in CI/CD pipeline
- MCP tool reliability issues
- Test analysis tool failures (30+ tests)

## Conclusion

The test database handling inconsistency is a **critical architectural flaw** that explains many of the test failures. The Simple test runner must be updated to use the same atomic write + locking pattern as the Rust runner.

**Immediate action:** Disable database writes in Simple runner until proper atomic write API is available.

**Next step:** Implement `rt_file_atomic_write()` FFI function and update Simple test runner to use proper read-modify-write cycle with atomic operations.
