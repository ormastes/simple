# Test Database Corruption Fix

## Date
2026-02-04

## Root Cause

The test database file `doc/test/test_db_runs.sdn` was corrupted with missing blank line terminators between tables.

**Error Message:**
```
Failed to parse V3 SDN: Invalid table row: expected 2 columns, found 1
```

**Issue:**
SDN format requires blank lines (double newlines `\n\n`) between tables. The file had:
```sdn
        25, new_test,
test_runs |run_id, start_time, end_time, ...|
```

Should have been:
```sdn
        25, new_test,

test_runs |run_id, start_time, end_time, ...|
```

## Analysis

### Serializer Code (CORRECT)
File: `src/app/test_runner_new/test_db_serializer.spl`

The `serialize_volatile_db` function correctly adds blank lines:
- Line 83: `parts.push("")` - after counters table
- Line 91: `parts.push("")` - after timing table
- Line 98: `parts.push("")` - after timing_runs table
- Line 104: `parts.push("")` - after changes table ✓
- Lines 111-112: `parts.push("")` twice - after test_runs table + final blank line

### Join Logic (CORRECT)
Line 114: `parts.join("\n")` correctly creates:
```
"table_header\nrow1\nrow2\n\nnext_table_header\n..."
```

The empty strings in the array create the blank lines when joined with `\n`.

### Why Corruption Occurred

The file was likely written by code that had a bug or by direct file manipulation that bypassed the serializer. Possible causes:

1. **Older code version**: File written before line 104 was added
2. **Concurrent writes**: Multiple processes writing simultaneously
3. **Incomplete write**: Write operation interrupted mid-stream
4. **String trimming**: Some code path trimming trailing newlines

## Fix Applied

### Manual Fix
Added missing blank line in `doc/test/test_db_runs.sdn`:
```diff
         25, new_test,
+
 test_runs |run_id, start_time, end_time, ...|
```

Also added final newline at end of file:
```bash
echo "" >> doc/test/test_db_runs.sdn
```

### Code Fix
The serializer code is already correct. No changes needed to serialization logic.

### I/O Implementation
Updated `src/app/io/mod.spl` to use pure Simple implementations via shell commands:
- `file_write`: Uses `printf '%s' > file`
- `file_atomic_write`: Uses temp file + `mv` for atomicity
- `shell`: Returns ProcessResult with exit_code for proper error checking

## Prevention

### Serializer Guarantees
The serializer ensures:
1. Every table followed by `parts.push("")`
2. File ends with double `parts.push("")` for final blank line
3. All newlines are `\n` (LF), never `\r\n` (CRLF)

### File Writing
- Always use `file_atomic_write` for database files
- Never manually edit database files
- Always validate after write using parser

### Testing
Added test coverage:
- Parse database after every write
- Verify blank lines between tables
- Check final newline exists

## Status
✅ **RESOLVED** - Database corruption fixed, serializer verified correct

## Related Files
- `src/app/test_runner_new/test_db_serializer.spl` - Serialization logic
- `src/app/test_runner_new/test_db_parser.spl` - Parsing logic
- `src/app/io/mod.spl` - File I/O implementation
- `doc/test/test_db_runs.sdn` - Database file (fixed)
