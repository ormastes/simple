# Stats Command User Guide

The `simple stats` command provides comprehensive project metrics and statistics.

## Basic Usage

### Default Output

Show all statistics with standard formatting:

```bash
simple stats
```

**Output:**
```
=========================================
Simple Project Statistics
=========================================

Collecting data...

Files:
  Total:   1,144 source files
    app:   518 files
    lib:   64 files
    std:   158 files
  Tests:   1,030 test files

Lines of Code:
  Total:   281,448 lines

Tests:
  Total:   27 tests
  Passed:  27 (100%)
  Status:  ✅ ALL PASSING

Features:
  Total:       68 features
  Complete:    64
  In Progress: 3
  Planned:     1

Documentation:
  Features:   doc/feature/feature.md
  Tests:      doc/test/test_result.md
  Bugs:       doc/bug/bug_report.md
  Pending:    doc/feature/pending_feature.md

=========================================
```

## Command-Line Flags

### --brief

Show condensed output without the documentation section:

```bash
simple stats --brief
```

Removes:
- "Collecting data..." message
- Documentation links section

### --verbose

Show extended output with additional details:

```bash
simple stats --verbose
```

Adds:
- Directory scan information
- Category descriptions

### --quick

Skip line counting for faster execution:

```bash
simple stats --quick
```

**Performance:**
- Full mode: ~2-3 seconds
- Quick mode: ~0.4 seconds

Use when you only need file/test/feature counts without LOC analysis.

### --json

Output statistics as JSON for CI/CD integration:

```bash
simple stats --json
```

**Output:**
```json
{
  "files": {
    "total": 1144,
    "app": 518,
    "lib": 64,
    "std": 158,
    "tests": 1030
  },
  "lines": {
    "total": 281448
  },
  "tests": {
    "total": 27,
    "passed": 27,
    "pass_rate": 100
  },
  "features": {
    "total": 68,
    "complete": 64,
    "in_progress": 3,
    "planned": 1
  }
}
```

## Combining Flags

Flags can be combined for custom output:

```bash
# Fast JSON output for CI/CD
simple stats --json --quick

# Detailed text output
simple stats --verbose

# Minimal text output
simple stats --brief --quick
```

## Use Cases

### CI/CD Integration

Parse JSON output in GitHub Actions, GitLab CI, etc.:

```yaml
# .github/workflows/stats.yml
- name: Collect statistics
  run: |
    bin/simple stats --json > stats.json

- name: Parse and display
  run: |
    cat stats.json | jq '.tests.pass_rate'
```

### Quick Status Check

Get fast overview without line counting:

```bash
simple stats --quick
```

### Project Health Dashboard

Combine with other commands for comprehensive view:

```bash
simple stats
simple test --list
cat doc/build/recent_build.md
```

### Tracking Progress

Monitor feature completion over time:

```bash
# Save baseline
simple stats --json > baseline.json

# ... work on features ...

# Compare
simple stats --json > current.json
diff baseline.json current.json
```

## Metrics Explained

### Files
- **Total**: Count of all .spl files in `src/`
- **app**: Application code in `src/app/`
- **lib**: Library code in `src/lib/`
- **std**: Standard library in `src/lib/`
- **Tests**: Test files in `test/`

### Lines of Code
- Total LOC across all source files
- Includes code, comments, and blank lines
- Computed via `wc -l`

### Tests
- **Total**: Test count from `doc/test/test_result.md`
- **Passed**: Number of passing tests
- **Pass Rate**: Percentage of tests passing
- **Status**: Visual indicator (✅ if all passing)

### Features
- **Total**: Features in `doc/feature/feature_db.sdn`
- **Complete**: Features marked as complete
- **In Progress**: Features being worked on
- **Planned**: Features not yet started

## Documentation References

The command shows links to detailed reports:

- **doc/feature/feature.md** - Complete feature index
- **doc/test/test_result.md** - Test results with timing
- **doc/bug/bug_report.md** - Bug tracking report
- **doc/feature/pending_feature.md** - Incomplete features only

## Performance Tips

1. **Use --quick** for fast checks (skips LOC counting)
2. **Use --json** in scripts (easier parsing)
3. **Use --brief** to reduce output noise
4. **Combine flags** for optimal output

## Troubleshooting

### Slow execution

If stats takes too long:
- Use `--quick` to skip line counting
- Check if filesystem is slow (network drive, etc.)
- Ensure `find`, `grep`, `wc` commands are available

### Missing statistics

If some metrics show 0:
- Check that database files exist:
  - `doc/test/test_result.md`
  - `doc/feature/feature_db.sdn`
- Run tests to generate test_result.md
- Ensure databases are up to date

### JSON parsing errors

If JSON output is malformed:
- Ensure you're only using `--json` flag
- Don't combine with `--verbose` (adds extra text)
- Pipe through `jq` to validate: `simple stats --json | jq .`

## Examples

### Daily Status Check
```bash
#!/bin/bash
# Morning project status
echo "=== Project Status ==="
simple stats --brief
echo ""
echo "=== Recent Build ==="
tail -20 doc/build/recent_build.md
```

### CI/CD Health Gate
```bash
#!/bin/bash
# Fail if test pass rate < 90%
PASS_RATE=$(simple stats --json --quick | jq -r '.tests.pass_rate')
if [ "$PASS_RATE" -lt 90 ]; then
  echo "Test pass rate below 90%: $PASS_RATE%"
  exit 1
fi
```

### Weekly Progress Report
```bash
#!/bin/bash
# Track feature completion
COMPLETE=$(simple stats --json --quick | jq -r '.features.complete')
TOTAL=$(simple stats --json --quick | jq -r '.features.total')
echo "Features: $COMPLETE/$TOTAL complete"
```

## See Also

- `simple test` - Run tests
- `simple build` - Build project
- `doc/test/test_result.md` - Detailed test results
- `doc/feature/feature.md` - Feature documentation
