# Unified Database Library Design

## Overview

Design for a shared atomic textual database library supporting Bug DB, Test DB, and Feature DB with common query features and reduced duplication.

## Architecture

```
src/lib/database/
├── mod.spl              # Base SdnDatabase class + StringInterner
├── atomic.spl           # Atomic file operations with locking
├── query.spl            # Shared query builder and filters
├── bug.spl              # BugDatabase (extends SdnDatabase)
├── test.spl             # TestDatabase (extends SdnDatabase)
└── feature.spl          # FeatureDatabase (extends SdnDatabase)
```

## Core Components

### 1. StringInterner (src/lib/database/mod.spl)

Efficient string deduplication shared by all databases.

```simple
class StringInterner:
    strings: Dict<text, i32>      # string -> id
    reverse: Dict<i32, text>      # id -> string
    next_id: i32

    # Create new interner
    static fn empty() -> StringInterner

    # Intern a string, return its ID
    me intern(s: text) -> i32

    # Get string by ID
    fn get(id: i32) -> text?

    # Load from SDN table
    static fn from_sdn(table: SdnTable) -> StringInterner

    # Export to SDN table
    fn to_sdn() -> SdnTable
```

### 2. AtomicFileOps (src/lib/database/atomic.spl)

Thread-safe file operations with locking.

```simple
class FileLock:
    path: text
    lock_path: text
    acquired: bool

    # Acquire lock (blocks until available)
    me acquire() -> bool

    # Release lock
    me release()

    # Try acquire with timeout
    me try_acquire(timeout_ms: i64) -> bool

fn atomic_read(path: text) -> text?
fn atomic_write(path: text, content: text) -> bool
fn atomic_append(path: text, content: text) -> bool
```

### 3. Base SdnDatabase (src/lib/database/mod.spl)

Shared base class for all databases.

```simple
class SdnDatabase:
    path: text                    # Path to .sdn file
    interner: StringInterner      # Shared string interner
    tables: Dict<text, SdnTable>  # All tables in database
    modified: bool                # Track if needs save

    # Create new database
    static fn new(path: text) -> SdnDatabase

    # Load existing database
    static fn load(path: text) -> SdnDatabase?

    # Save to disk (atomic)
    me save() -> bool

    # Get table by name
    fn get_table(name: text) -> SdnTable?

    # Add or update table
    me set_table(name: text, table: SdnTable)

    # Common queries (implemented by query.spl)
    fn query(table: text) -> QueryBuilder

    # String interning helpers
    me intern(s: text) -> i32
    fn resolve(id: i32) -> text?

    # Validation
    fn validate() -> [text]  # Returns list of errors
```

### 4. QueryBuilder (src/lib/database/query.spl)

Fluent query interface for common operations.

```simple
class QueryBuilder:
    table: SdnTable
    filters: [Filter]
    sort_by: text?
    limit: i64?

    # Add filter condition
    me where(field: text, op: CompareOp, value: text) -> QueryBuilder

    # Filter by multiple values
    me where_in(field: text, values: [text]) -> QueryBuilder

    # Exclude soft-deleted rows
    me only_valid() -> QueryBuilder

    # Sort results
    me order_by(field: text, desc: bool) -> QueryBuilder

    # Limit results
    me take(n: i64) -> QueryBuilder

    # Execute query
    fn execute() -> [SdnRow]

    # Count results
    fn count() -> i64

    # Check if any match
    fn exists() -> bool

enum CompareOp:
    Eq | Ne | Gt | Ge | Lt | Le | Contains | StartsWith | EndsWith

struct Filter:
    field: text
    op: CompareOp
    value: text
```

### 5. SdnTable and SdnRow (src/lib/database/mod.spl)

In-memory representation of SDN tables.

```simple
class SdnTable:
    name: text
    columns: [text]               # Column names
    rows: [SdnRow]                # All rows
    index: Dict<text, i64>        # Primary key -> row index

    # Create new table
    static fn new(name: text, columns: [text]) -> SdnTable

    # Parse from SDN format
    static fn parse(content: text) -> SdnTable?

    # Export to SDN format
    fn to_sdn() -> text

    # Add row
    me add_row(row: SdnRow) -> bool

    # Update row by primary key
    me update_row(key: text, row: SdnRow) -> bool

    # Get row by primary key
    fn get_row(key: text) -> SdnRow?

    # Soft delete (set valid=false)
    me mark_deleted(key: text) -> bool

    # Get all valid rows
    fn valid_rows() -> [SdnRow]

struct SdnRow:
    fields: Dict<text, text>      # column -> value

    fn get(column: text) -> text?
    fn get_i64(column: text) -> i64?
    fn get_bool(column: text) -> bool?
    me set(column: text, value: text)
```

## Domain-Specific Extensions

### BugDatabase (src/lib/database/bug.spl)

```simple
class BugDatabase:
    db: SdnDatabase

    # Factory methods
    static fn load(path: text) -> BugDatabase?
    static fn create(path: text) -> BugDatabase

    # High-level operations
    me add_bug(bug: Bug) -> bool
    me update_bug(id: text, bug: Bug) -> bool
    fn get_bug(id: text) -> Bug?
    fn all_bugs() -> [Bug]
    fn bugs_by_status(status: BugStatus) -> [Bug]
    fn bugs_by_severity(severity: BugSeverity) -> [Bug]
    fn critical_bugs() -> [Bug]  # P0 + P1
    fn open_bugs() -> [Bug]      # Open + Investigating + Confirmed

    # Validation
    fn validate_test_links() -> [text]  # Check all bugs link to real tests
    fn validate_fix_strategy() -> [text]  # Check P0/P1 have strategy

    # Statistics
    fn stats() -> BugStats

struct Bug:
    id: text
    severity: BugSeverity
    status: BugStatus
    title: text
    description: [text]
    file: text
    line: i64
    reproducible_by: text
    fix_strategy: [text]
    investigation_log: [text]
    created_at: text
    updated_at: text
    valid: bool

struct BugStats:
    total: i64
    open: i64
    fixed: i64
    p0: i64
    p1: i64
    important: i64
    health: text  # "good" | "attention" | "critical"
```

### TestDatabase (src/lib/database/test.spl)

```simple
class TestDatabase:
    db: SdnDatabase

    # Factory methods
    static fn load(path: text) -> TestDatabase?
    static fn create(path: text) -> TestDatabase

    # Test run management
    me start_run() -> text  # Returns run_id
    me end_run(run_id: text, status: RunStatus) -> bool
    me add_result(run_id: text, result: TestResult) -> bool

    # Queries
    fn get_run(run_id: text) -> TestRun?
    fn recent_runs(n: i64) -> [TestRun]
    fn get_result(test_name: text, run_id: text) -> TestResult?
    fn test_history(test_name: text, limit: i64) -> [TestResult]

    # Analysis
    fn flaky_tests(threshold: f64) -> [text]  # Tests with <threshold pass rate
    fn slow_tests(percentile: i64) -> [(text, f64)]  # 95th percentile times
    fn calculate_percentile(test_name: text, p: i64) -> f64?

    # Cleanup
    me cleanup_stale_runs() -> i64  # Mark crashed, return count
    me prune_old_runs(keep: i64) -> i64  # Keep N most recent, return deleted

struct TestRun:
    run_id: text
    start_time: text
    end_time: text?
    pid: i64
    hostname: text
    status: RunStatus
    test_count: i64
    passed: i64
    failed: i64
    crashed: i64
    timed_out: i64

struct TestResult:
    test_name: text
    run_id: text
    status: TestStatus
    duration_ms: f64
    error_message: text?
    timestamp: text

enum RunStatus: Running | Completed | Crashed | TimedOut | Interrupted
enum TestStatus: Passed | Failed | Crashed | TimedOut | Skipped
```

### FeatureDatabase (src/lib/database/feature.spl)

```simple
class FeatureDatabase:
    db: SdnDatabase

    # Factory methods
    static fn load(path: text) -> FeatureDatabase?
    static fn create(path: text) -> FeatureDatabase

    # Operations
    me add_feature(feature: Feature) -> bool
    me update_feature(id: text, feature: Feature) -> bool
    fn get_feature(id: text) -> Feature?
    fn all_features() -> [Feature]
    fn features_by_category(category: text) -> [Feature]
    fn features_by_status(status: FeatureStatus) -> [Feature]

    # Mode matrix queries
    fn features_by_mode(mode: FeatureMode) -> [Feature]
    fn incomplete_features() -> [Feature]  # Any mode not "done"

    # Categories
    fn all_categories() -> [text]
    fn category_stats(category: text) -> CategoryStats

    # Validation
    fn validate_specs() -> [text]  # Check spec files exist

struct Feature:
    id: text
    category: text
    name: text
    description: text
    spec_file: text
    pure_status: FeatureStatus
    hybrid_status: FeatureStatus
    llvm_status: FeatureStatus
    created_at: text
    updated_at: text
    valid: bool

struct CategoryStats:
    category: text
    total: i64
    done: i64
    in_progress: i64
    planned: i64
    failed: i64

enum FeatureStatus: Done | InProgress | Planned | Failed | Blocked
enum FeatureMode: Pure | Hybrid | LLVM
```

## Usage Examples

### Bug Database

```simple
from lib.database.bug import BugDatabase, Bug, BugSeverity, BugStatus

# Load database
val bugdb = BugDatabase.load("doc/bug/bug_db.sdn")?

# Add new bug
val bug = Bug(
    id: "parser_001",
    severity: BugSeverity.P1,
    status: BugStatus.Open,
    title: "Parser crashes on multiline",
    description: ["Parser fails when...", "Expected behavior..."],
    file: "src/app/parser/core.spl",
    line: 123,
    reproducible_by: "test_multiline_parse",
    fix_strategy: ["Add line continuation support"],
    investigation_log: [],
    created_at: timestamp_now(),
    updated_at: timestamp_now(),
    valid: true
)
bugdb.add_bug(bug)
bugdb.db.save()

# Query bugs
val critical = bugdb.critical_bugs()
val open = bugdb.open_bugs()

# Validate
val errors = bugdb.validate_test_links()
if errors.?:
    print "Validation errors: {errors}"
```

### Test Database

```simple
from lib.database.test import TestDatabase, TestResult, TestStatus

# Load database
val testdb = TestDatabase.load("doc/test/test_db.sdn")?

# Start test run
val run_id = testdb.start_run()

# Add results
val result = TestResult(
    test_name: "parser_spec::test_basic",
    run_id: run_id,
    status: TestStatus.Passed,
    duration_ms: 123.45,
    error_message: None,
    timestamp: timestamp_now()
)
testdb.add_result(run_id, result)

# End run
testdb.end_run(run_id, RunStatus.Completed)
testdb.db.save()

# Analyze
val flaky = testdb.flaky_tests(0.95)  # <95% pass rate
val slow = testdb.slow_tests(95)      # 95th percentile
```

### Feature Database

```simple
from lib.database.feature import FeatureDatabase, Feature, FeatureStatus

# Load database
val featdb = FeatureDatabase.load("doc/feature/feature_db.sdn")?

# Query features
val incomplete = featdb.incomplete_features()
val parser_features = featdb.features_by_category("parser")

# Check category progress
val stats = featdb.category_stats("parser")
print "Parser: {stats.done}/{stats.total} done"
```

## Implementation Plan

### Phase 1: Core Infrastructure
1. Implement StringInterner
2. Implement AtomicFileOps
3. Implement SdnTable and SdnRow
4. Implement base SdnDatabase class

### Phase 2: Query Layer
1. Implement QueryBuilder
2. Add common query operations
3. Add filtering and sorting

### Phase 3: Domain Extensions
1. Implement BugDatabase
2. Implement TestDatabase
3. Implement FeatureDatabase

### Phase 4: Testing
1. Unit tests for each component
2. Integration tests for full workflows
3. Performance tests for large databases

### Phase 5: Migration
1. Migrate existing bug_db.sdn to new format
2. Migrate existing test_db.sdn to new format
3. Migrate existing feature_db.sdn to new format
4. Update all callers to use new API

## Key Design Decisions

### 1. Inheritance vs Composition
- **Decision**: Use composition (SdnDatabase as field in domain classes)
- **Reason**: Simple doesn't have full inheritance yet, composition is clearer

### 2. String Interning
- **Decision**: Share StringInterner across all tables in a database
- **Reason**: Reduces memory, consistent IDs within database file

### 3. Atomic Operations
- **Decision**: Lock at file level, not table level
- **Reason**: Simpler, prevents partial writes, good enough for current scale

### 4. Query Builder
- **Decision**: Fluent interface with method chaining
- **Reason**: Ergonomic, type-safe, similar to SQL ORMs

### 5. Soft Deletes
- **Decision**: Use `valid` boolean flag, never hard delete
- **Reason**: Preserves history, simplifies implementation, common pattern

### 6. Multiline Fields
- **Decision**: Use `[text]` arrays, not `<<<...>>>` delimiters
- **Reason**: Type-safe, easier to query, consistent with Simple idioms

## Testing Strategy

### Unit Tests
- StringInterner: intern, get, load, save
- AtomicFileOps: concurrent reads/writes, lock timeout
- SdnTable: parse, export, add, update, delete
- QueryBuilder: filters, sorting, limits

### Integration Tests
- Full workflow: create database, add entries, query, save, load
- Concurrent access: multiple processes reading/writing
- Large databases: 10,000+ entries

### Performance Tests
- String interning: 100,000 strings
- Query performance: 10,000 rows with filters
- Save/load time: large databases

## Success Criteria

1. ✅ All three databases use shared library
2. ✅ No code duplication in common operations
3. ✅ Thread-safe atomic operations
4. ✅ Fluent query API
5. ✅ All existing functionality preserved
6. ✅ All tests pass
7. ✅ Performance acceptable (no regressions)

## Next Steps

1. Implement Phase 1 (Core Infrastructure)
2. Write unit tests for core components
3. Implement Phase 2 (Query Layer)
4. Test query functionality
5. Implement Phase 3 (Domain Extensions)
6. Integration tests and migration
