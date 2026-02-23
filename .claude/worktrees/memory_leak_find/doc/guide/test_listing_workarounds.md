# Test Listing Performance Workarounds

Quick reference for fast test discovery and listing.

## The Problem

```bash
# ⚠️ SLOW - scans all 8000+ tests
./target/release/simple test --only-skipped --list
```

**Why it's slow:** List mode still executes every test file to discover which tests match the filter.

## ✅ Fast Workarounds

### Option 1: Use Test Database (Instant)

The test database is updated after every test run and contains all test metadata.

```bash
# Find all skipped tests
cat doc/test/test_db.sdn | grep '"skip"'

# Find slow tests
cat doc/test/test_db.sdn | grep '"slow"'

# Find specific test
cat doc/test/test_db.sdn | grep "my_test_name"

# Get test counts by status
cat doc/test/test_db.sdn | grep '"status"' | sort | uniq -c
```

**Pros:** Instant, no execution needed
**Cons:** Only shows tests from last run

### Option 2: Limit Scope with Path

Scan only specific directories or files.

```bash
# ✅ Fast - scan one directory
./target/release/simple test test/lib/std/unit/syntax/ --only-skipped --list

# ✅ Fast - scan specific file
./target/release/simple test test/lib/std/unit/core/dsl_spec.spl --only-skipped --list

# ✅ Fast - scan multiple specific paths
./target/release/simple test test/lib/std/unit/core/ test/lib/std/unit/collections/ --only-skipped --list
```

**Pros:** Shows current state, can focus on areas
**Cons:** Need to know which paths to check

### Option 3: Just Run Filtered Tests

Instead of listing, just run them (often faster than scanning all files to list).

```bash
# Run only skipped tests (usually fail, showing what's not implemented)
./target/release/simple test --only-skipped

# Run only slow tests
./target/release/simple test --only-slow

# Run with specific tag
./target/release/simple test --tag=integration
```

**Pros:** Actually runs the tests, validates they work
**Cons:** Takes longer than listing (but might be faster than full scan)

### Option 4: Use grep on Source Files

Search for test definitions directly in source code.

```bash
# Find all 'skip' tagged tests
grep -r "skip" test/lib/std/ --include="*.spl" | grep -E '(it|describe|context)' | head -20

# Find slow tests
grep -r "slow_it" test/lib/std/ --include="*.spl"

# Count skipped tests per directory
find test/lib/std/ -name "*.spl" -exec grep -l '"skip"' {} \; | wc -l
```

**Pros:** Very fast, works on any codebase state
**Cons:** Regex-based, might miss some edge cases

## Comparison

| Method | Speed | Accuracy | Use Case |
|--------|-------|----------|----------|
| **Test Database** | ⚡⚡⚡ Instant | Last run only | Quick lookup |
| **Scoped Path** | ⚡⚡ Fast | 100% current | Focused areas |
| **Run Filtered** | ⚡ Medium | 100% + validation | Actually test |
| **grep Source** | ⚡⚡⚡ Instant | 95% (regex) | Quick count |
| **Full List** | 🐌 Very slow | 100% current | Don't use |

## Examples

### Find What's Not Implemented

```bash
# Quick lookup in test database
cat doc/test/test_db.sdn | grep '"skip"' | wc -l
# Shows: 1,241 skipped tests

# See which areas have most skipped tests
cat doc/test/test_db.sdn | grep '"skip"' | grep -o 'test/[^/]*/[^/]*/' | sort | uniq -c | sort -rn | head -10
```

### Check Specific Feature Area

```bash
# Check physics tests only
./target/release/simple test test/lib/std/unit/physics/ --list --show-tags

# Check if specific test is skipped
grep -r "my_feature_test" test/ --include="*.spl" -A 2 | grep skip
```

### Validate Slow Tests

```bash
# Run all slow tests to see if they actually work
./target/release/simple test --only-slow

# List slow tests in specific area
./target/release/simple test test/lib/std/integration/ --only-slow --list
```

## Best Practices

1. **Regular development:** Use test database for quick lookups
2. **Focused work:** Use scoped paths when working on specific features
3. **Validation:** Run filtered tests to ensure they work
4. **Bulk queries:** Use grep for counts and statistics

## Future Improvements

**Planned (P1):**
- Fast list mode with AST-only parsing
- Test index cache for instant listing
- Better integration with test database

**Workarounds remain valid** even after improvements!

## See Also

- **Issue Report:** `doc/report/test_listing_issue_2026-01-22.md`
- **Test Database:** `doc/test/test_db.sdn`
- **Test Results:** `doc/test/test_result.md`
