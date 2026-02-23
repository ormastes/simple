# Dashboard Database

This directory contains the SDN (Simple Data Notation) database files for the dashboard system.

## Structure

```
doc/dashboard/
├── tables/              # Current state tables
│   ├── features.sdn
│   ├── sspec_tests.sdn
│   ├── todos.sdn
│   ├── coverage.sdn
│   ├── duplication.sdn
│   ├── test_status.sdn
│   ├── verification.sdn
│   ├── vcs_state.sdn
│   ├── build_times.sdn
│   ├── dependencies.sdn
│   └── plans.sdn
├── history/             # Historical snapshots (90-day retention)
│   └── YYYY-MM/
│       └── YYYY-MM-DD.sdn
└── dashboard_db.cache.sdn  # Fast summary cache (30s TTL)
```

## Table Schemas

### features.sdn
Tracks language features and their implementation status across different execution modes.
```
features |id, category, name, status, test_coverage, last_updated|
```

### sspec_tests.sdn
Tracks SSpec BDD test files and their execution results.
```
sspec_tests |id, file, title, category, difficulty, status, total_tests, passed, failed, duration_ms, has_docs, last_run|
```

### todos.sdn
Extended TODO tracking with age, assignees, and status.
```
todos |id, keyword, area, priority, description, file, line, issue, blocked, status, age_days, assigned, last_updated|
```

### coverage.sdn
Code coverage metrics at file, crate, and workspace levels.
```
coverage |id, level, crate, file, lines_total, lines_covered, lines_percent, branches_covered, branches_percent, timestamp|
```

### duplication.sdn
Code duplication detection results.
```
duplication |id, file1, file2, lines, tokens, percentage, timestamp|
```

### test_status.sdn
Test execution results by mode (unit, integration, system).
```
test_status |id, mode, suite, total, passed, failed, skipped, duration_ms, timestamp|
```

### verification.sdn
Lean 4 verification status for formally verified properties.
```
verification |id, module, property, status, proof_lines, timestamp|
```

### vcs_state.sdn
Current version control system state (Jujutsu).
```
vcs_state |bookmark, commit_id, commit_message, uncommitted_files, untracked_files, timestamp|
```

### build_times.sdn
Compilation duration tracking for performance monitoring.
```
build_times |id, timestamp, target, mode, duration_ms, crates_compiled, incremental, commit_id|
```

### dependencies.sdn
Cargo dependency health and update tracking.
```
dependencies |id, crate_name, current_version, latest_version, outdated, has_security_issue, last_checked|
```

### plans.sdn
Implementation plan tracking from `.claude/plans/`.
```
plans |id, file, title, status, created, last_updated, total_steps, completed_steps, blocked|
```

## Usage

### Collect Data
```bash
simple dashboard collect --mode=full
```

### View CLI Dashboard
```bash
simple dashboard              # Summary view
simple dashboard sspec        # SSpec details
simple dashboard todos        # TODO breakdown
simple dashboard coverage     # Coverage details
```

### Web Dashboard
```bash
simple dashboard serve --port 3000
```

### Export Reports
```bash
simple dashboard export --format=html > report.html
simple dashboard export --format=json > data.json
```

## Cache Management

The dashboard uses a 30-second TTL cache to avoid frequent re-scans:

- Cache file: `dashboard_db.cache.sdn`
- TTL: 30 seconds
- Invalidation: Automatic on data collection
- Manual invalidation: `simple dashboard invalidate-cache`

## Historical Snapshots

Daily snapshots are saved for trend analysis:

- Location: `history/YYYY-MM/YYYY-MM-DD.sdn`
- Retention: 90 days
- Cleanup: Automatic during collection
- Manual snapshot: `simple dashboard snapshot`

## Data Collection Schedule

Recommended collection frequency:

- **Continuous Integration**: On every commit
- **Development**: On-demand or every 5 minutes (watch mode)
- **Historical**: Daily snapshot at midnight

## Performance

Collection performance targets:

- Full scan: <5 seconds
- Incremental: <1 second
- Cache hit: <100ms
- Database read: <200ms

## Migration from Existing Databases

The dashboard reuses existing data sources:

- `doc/todo/todo_db.sdn` → `tables/todos.sdn` (extended schema)
- `doc/feature/feature_db.sdn` → `tables/features.sdn` (compatible)
- `doc/task/task_db.sdn` → `tables/plans.sdn` (integrated)

Migration is automatic during first collection.
