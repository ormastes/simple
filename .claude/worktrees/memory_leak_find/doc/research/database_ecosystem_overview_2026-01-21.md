# Database Ecosystem Overview

**Date:** 2026-01-21
**Status:** Unified Design
**Purpose:** Overview of all textual databases in the Simple project

## Database Systems

The Simple project uses four complementary textual database systems, all following the same architectural pattern:

1. **TODO Database** - Track TODOs and FIXMEs in source code
2. **Feature Database** - Track test-driven feature implementation status
3. **Test Result Database** - Track test execution results (pass/fail) and timing with variance management
4. **Build Database** - Track compilation errors and warnings

## Architectural Pattern

All databases follow this unified pattern:

```
Command → Database Update → Documentation Generation
  ↓            ↓                      ↓
Run     Save to SDN file      Generate markdown docs
```

### Comparison Table

| System | Command | Database File | Generated Docs | Updated When | Purpose |
|--------|---------|---------------|----------------|--------------|---------|
| **TODO** | `simple todo-scan` | `doc/todo/todo_db.sdn` | `doc/TODO.md` | Manual | Track code TODOs |
| **Feature** | `simple test` | `doc/feature/feature_db.sdn` | `doc/feature/*.md` | Every test run | Track feature status |
| **Test Results** | `simple test` | `doc/test/test_db.sdn` | `doc/test/test_result.md` | Every test run | Track test status + timing |
| **Build** | `simple build` | `doc/build/build_db.sdn` | `doc/build/recent_build.md` | Every build | Track build errors |

## Integration Points

### 1. Test System Integration

**When running `simple test`:**

```rust
fn run_tests() {
    // 1. Execute tests
    let test_results = execute_test_suite();

    // 2. Update feature database (existing)
    update_feature_db(&test_results);
    generate_feature_docs();  // → doc/feature/*.md (feature-centric view)

    // 3. Update test result database (new)
    update_test_result_db(&test_results);
    generate_test_result_docs();   // → doc/test/test_result.md (test-centric view)

    // 4. Link bugs to failing tests
    update_bug_links(&test_results);
}
```

### 2. Build System Integration

**When running `simple build`:**

```rust
fn run_build() {
    // 1. Execute build
    let build_results = execute_cargo_build();

    // 2. Update build database (new)
    update_build_db(&build_results);
    generate_build_docs();  // → doc/build/recent_build.md
}
```

### 3. Bug Database Integration

**Bugs link to all systems:**

```sdn
{
  bug_id: "bug_042"

  # Link to feature
  feature_id: "feature_http_client_error_handling"

  # Link to reproducible test (REQUIRED)
  reproducible_by: ["test_http_client_malformed_response"]

  # Link to test timing (if performance bug)
  timing_impact: {
    affected_tests: ["test_http_client_malformed_response"]
    regression_pct: 150.0
  }

  # Link to build errors (if causes compilation issues)
  build_impact: {
    causes_errors: true
    error_codes: ["E0308", "E0425"]
    affected_files: ["src/lib/std/src/compiler_core/net/http_client.spl"]
  }
}
```

## Feature vs Test Views

The system provides two complementary views of test results:

### `doc/feature/pending_feature.md` - Feature-Centric View

**Focus:** What features need implementation work?

**Contents:**
- Features grouped by status (failed, in_progress, planned)
- Features grouped by category
- Overall feature completion percentage
- Which features are blocking

**Use When:**
- Planning feature development
- Tracking feature progress
- Prioritizing incomplete features
- Project management perspective

**Example:**
```markdown
# Pending Features

## 🔴 Failed Features (3)
### Category: Network
- feature_http_client_error_handling (3 tests, all failing)

## 🟡 In Progress Features (12)
### Category: Runtime
- feature_gc_concurrent (5 tests, 2 passing, 3 failing)
```

### `doc/test/test_result.md` - Test-Centric View

**Focus:** Which tests failed and why?

**Contents:**
- Tests grouped by status (passed, failed, skipped)
- Failure details (error messages, stack traces)
- Timing analysis and performance regressions
- Flaky test detection
- Individual test execution history

**Use When:**
- Debugging test failures
- Investigating performance regressions
- Finding flaky tests
- Developer troubleshooting perspective

**Example:**
```markdown
# Test Results

## ❌ Failed Tests (3)

### test_http_client_malformed_response
**Error:** Assertion failed: index out of bounds
**Location:** http_client_spec.spl:145
**Timing:** 67.3ms (baseline: 45.2ms, +48.9% regression)
**Linked Bugs:** bug_042
```

### Comparison

| Aspect | pending_feature.md | test_result.md |
|--------|-------------------|----------------|
| **Perspective** | Feature development | Test execution |
| **Grouping** | By feature | By test |
| **Status** | Feature completion | Test pass/fail |
| **Timing** | Not included | Detailed timing analysis |
| **Errors** | Not included | Full error messages + stack traces |
| **Use Case** | What to build next | What's broken and why |

**Both are generated automatically on every test run from the same underlying data.**

## Workflow Examples

### Example 1: Feature Development

```bash
# Developer works on new feature
jj commit -m "Add HTTP client error handling"

# Build to check for errors
simple build
# → Updates doc/build/recent_build.md
# → Shows any compilation errors

# Run tests
simple test
# → Updates doc/feature/feature_db.sdn
# → Updates doc/test/test_db.sdn
# → Generates doc/feature/pending_feature.md
# → Generates doc/test/test_result.md

# Check status
cat doc/feature/pending_feature.md   # See incomplete features (feature view)
cat doc/test/test_result.md          # See test failures + timing (test view)
cat doc/build/recent_build.md        # See build errors
```

### Example 2: Bug Fixing

```bash
# Bug reported: test_http_client fails

# Create bug record with required test link
simple bug-add \
  --id=bug_042 \
  --title="HTTP client crashes on malformed response" \
  --reproducible-by=test_http_client_malformed_response

# Run test to confirm failure
simple test test/lib/std/unit/core/net/http_client_spec.spl
# → Test fails, timing recorded
# → Bug status: confirmed (has failing test)

# Fix the bug
vim src/lib/std/src/compiler_core/net/http_client.spl

# Build to check for new errors
simple build
# → No errors, build succeeds

# Run test again
simple test test/lib/std/unit/core/net/http_client_spec.spl
# → Test passes
# → Bug status: fixed (test now passing)
# → Timing baseline updated (if significant change)

# Verify in docs
cat doc/bug/bug_report.md
# → Shows bug_042 as fixed
```

### Example 3: Performance Regression Detection

```bash
# Developer makes optimization
jj commit -m "Optimize HTTP parsing"

# Run tests
simple test
# → Test timing database detects regression
# → test_http_parse: 45ms → 125ms (+177%)
# → ALERT: Exceeds 10% threshold

# Output:
Performance Regression Detected:
  test_http_parse: +177% (baseline: 45ms, new: 125ms)
  Threshold: 10%
  Statistical significance: 6.2 std_dev above mean

# Check timing report
cat doc/test/test_result.md
# → Shows regression details
# → Lists affected tests
# → Suggests investigating recent changes

# Developer investigates and fixes
# ... fix code ...

# Run tests again
simple test
# → test_http_parse: 125ms → 42ms (-66%)
# → Timing improved from baseline
# → Baseline updated: 45ms → 42ms
```

### Example 4: Build Error Tracking

```bash
# Developer breaks build
jj commit -m "Refactor type system"

# Build fails
simple build
# → 8 errors, 23 warnings
# → Updates doc/build/recent_build.md

# Check build report
cat doc/build/recent_build.md

# Output shows:
# ❌ FAILED - 8 errors, 23 warnings
# Top errors:
#   - E0308: Type mismatch (3 files)
#   - E0425: Undefined reference (2 files)
# Trend: 🔴 Regressing (prev: 4 errors)

# Fix errors one by one
vim src/rust/compiler/src/hir/lower/expr/literals.rs

# Build again
simple build
# → 5 errors, 23 warnings
# → Trend: 🟢 Improving (-3 errors)

# Continue fixing until clean build
simple build
# → ✅ SUCCESS - 0 errors, 18 warnings
# → Trend: 🟢 Improving (-5 errors, -5 warnings)
```

## Data Flow Diagram

```
Source Code
    ↓
┌───────────────────────────────────────────────────────┐
│                                                       │
│  simple todo-scan    → TODO Database   → TODO.md     │
│  simple test         → Feature DB      → feature/*.md │
│  simple test         → Test Timing DB  → test_result.md │
│  simple build        → Build DB        → recent_build.md │
│                                                       │
└───────────────────────────────────────────────────────┘
    ↓
Documentation (doc/)
    ↓
Developer/CI Consumption
```

## Unified Database Schema Principles

All databases follow these principles:

### 1. SDN Format

```sdn
{
  version: "1.0"
  last_updated: "2026-01-21T10:30:00Z"

  # Current state
  current_data: { ... }

  # Historical data
  history: [ ... ]

  # Configuration
  config: { ... }
}
```

### 2. Timestamp Tracking

Every database tracks:
- `last_updated` - When database was last modified
- Per-record timestamps - When each record was created/updated

### 3. Historical Data

All databases maintain history:
- TODO: Previous scan results
- Feature: Test run history
- Test Timing: Last 40 runs per test
- Build: Last 10 builds

### 4. Configuration

All databases support configuration:
- Global defaults
- Per-item overrides (per-test, per-file, etc.)
- Thresholds and limits

### 5. Auto-Generation

All databases auto-generate documentation:
- Markdown format
- Human-readable
- Actionable (show what needs work)
- Sortable/filterable

## File Organization

```
doc/
├── TODO.md                           # Generated by todo-scan
├── todo/
│   └── todo_db.sdn                   # TODO database
├── feature/
│   ├── feature_db.sdn                # Feature database
│   ├── feature.md                    # Generated feature index
│   ├── pending_feature.md            # Generated pending features
│   └── category/*.md                 # Generated per-category
├── test/
│   ├── test_db.sdn                   # Test result database (status + timing)
│   └── test_result.md                # Generated test results (failures + timing)
├── build/
│   ├── build_db.sdn                  # Build error database
│   └── recent_build.md               # Generated build report
└── bug/
    ├── bug_db.sdn                    # Bug database
    └── bug_report.md                 # Generated bug report
```

## CLAUDE.md Documentation

Update auto-generated documentation table:

```markdown
### Auto-Generated Documentation

Files automatically updated during development:

| File | Updated When | Command | Description |
|------|-------------|---------|-------------|
| `doc/TODO.md` | Manual | `simple todo-scan` | TODO/FIXME tracking from source code |
| `doc/feature/feature_db.sdn` | Every test run | `simple test` | Feature database (all features) |
| `doc/feature/feature.md` | Every test run | `simple test` | Feature index by category |
| `doc/feature/pending_feature.md` | Every test run | `simple test` | Incomplete features only |
| `doc/feature/category/*.md` | Every test run | `simple test` | Per-category feature lists |
| `doc/test/test_db.sdn` | Every test run | `simple test` | Test result database (status + timing) |
| `doc/test/test_result.md` | Every test run | `simple test` | Test results (pass/fail + timing analysis) |
| `doc/build/build_db.sdn` | Every build | `simple build` | Build error/warning database |
| `doc/build/recent_build.md` | Every build | `simple build` | Build errors and warnings report |
| `doc/bug/bug_db.sdn` | Manual | `simple bug-add` | Bug tracking database |
| `doc/bug/bug_report.md` | Manual | `simple bug-gen` | Bug status report |

**Quick Access:**
- **What needs work?** → `doc/feature/pending_feature.md` (feature-centric, updated every test run)
- **Test failures?** → `doc/test/test_result.md` (test-centric with timing, updated every test run)
- **Build status?** → `doc/build/recent_build.md` (updated every build)
- **All TODOs?** → `doc/TODO.md` (run `simple todo-scan` to update)
- **All bugs?** → `doc/bug/bug_report.md` (run `simple bug-gen` to update)
```

## Implementation Status

| System | Research | Schema | Implementation | Testing | Documentation | Status |
|--------|----------|--------|----------------|---------|---------------|--------|
| TODO | ✅ | ✅ | ✅ | ✅ | ✅ | **Complete** |
| Feature | ✅ | ✅ | ✅ | ✅ | ✅ | **Complete** |
| Test Results | ✅ | ✅ | ⏳ | ⏳ | ⏳ | **Researched** |
| Build | ✅ | ✅ | ⏳ | ⏳ | ⏳ | **Designed** |
| Bug | ✅ | ✅ | ⏳ | ⏳ | ⏳ | **Designed** |

## Benefits of Unified Approach

### 1. Consistency

All systems use same patterns:
- SDN format
- Auto-generation
- History tracking
- Configuration

**Benefit:** Easy to learn, predictable behavior

### 2. Integration

Systems reference each other:
- Bugs → Tests
- Tests → Features
- Features → TODOs
- Build Errors → Files → TODOs

**Benefit:** Complete traceability

### 3. Automation

Everything auto-generates:
- No manual documentation updates
- Always synchronized with code
- CI-friendly

**Benefit:** Always up-to-date

### 4. Visibility

Quick status checks:
- `cat doc/feature/pending_feature.md` - What needs work?
- `cat doc/build/recent_build.md` - Build status?
- `cat doc/test/test_result.md` - Performance?
- `cat doc/TODO.md` - Code TODOs?

**Benefit:** Single source of truth

## Related Documentation

### Research Documents
- `doc/research/test_timing_database_research_2026-01-21.md` - Test timing database design
- `doc/research/build_error_database_design_2026-01-21.md` - Build error database design

### Implementation Reports
- `doc/report/implementation_summary_2026-01-21.md` - TODO/Feature auto-generation
- `doc/report/auto_doc_generation_implementation_2026-01-21.md` - Auto-doc implementation details

### Skills
- `.claude/skills/todo.md` - TODO format and workflow
- `.claude/skills/sspec.md` - Feature testing workflow
- `.claude/skills/test.md` - Test writing guidance

---

**End of Overview**
