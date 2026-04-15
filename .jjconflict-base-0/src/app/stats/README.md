# Statistics Module

Provides the `simple stats` command to display project metrics.

## Current Implementation

**Active:** `dynamic.spl` - Dynamically computes statistics using shell commands

## Usage

```bash
# Show statistics
simple stats

# Brief output (no docs section)
simple stats --brief

# Verbose output (with directory details)
simple stats --verbose
```

## Statistics Displayed

- **Files**: Source file counts by category (app/lib/std)
- **Lines of Code**: Total LOC in source files
- **Tests**: Test counts and pass rates from test_result.md
- **Features**: Feature counts by status from feature_db.sdn
- **Documentation**: Links to detailed reports

## Implementation Notes

### Dynamic Approach (Current)

Uses `process_run` to execute shell commands for counting:
- `find` for file counts
- `grep -c` for pattern matching in databases
- `wc -l` for line counting

### Future Modules (Prepared)

- `types.spl` - Data structures for statistics
- `file_scanner.spl` - Directory walking logic
- `line_counter.spl` - LOC analysis
- `db_aggregator.spl` - Database parsing
- `formatter.spl` - Output formatting
- `main.spl` - Full implementation (blocked by runtime issues)

## Performance

Typical execution time: 2-3 seconds for full project scan

## See Also

- Test results: `doc/test/test_result.md`
- Feature tracking: `doc/feature/feature.md`
- Build status: `doc/build/recent_build.md`
