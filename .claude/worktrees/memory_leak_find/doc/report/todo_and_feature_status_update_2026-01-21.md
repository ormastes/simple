# TODO Status and Feature Status Update Mechanisms

**Date:** 2026-01-21
**Purpose:** Document who updates TODO status and feature status, when, and where

## Summary

| System | What Updates It | When | Where |
|--------|----------------|------|-------|
| **TODO Status** | Simple Collector (auto-inference) | Dashboard collection | `todo_collector.spl:86` |
| **TODO Status** | Manual SDN edit | Anytime | `doc/todos.sdn` (if exists) |
| **Feature Status** | Test runner | After test execution | `test_runner/feature_db.rs:39` |
| **Feature Status** | Manual SDN edit | Anytime | `doc/feature/feature_db.sdn` |

## 1. TODO Status Updates

### Who Updates TODO Status?

**Answer:** Two systems update TODO status:

#### A. Simple Language Collector (Automatic)

**File:** `src/lib/std/src/tooling/dashboard/collectors/todo_collector.spl`

**Function:** `infer_todo_status()` (lines 86-94)

```simple
fn infer_todo_status(todo: ParserTodoItem) -> text:
    # If blocked, mark as blocked
    if todo.blocked.len() > 0:
        return "blocked"

    # If has issue number, assume in progress
    match todo.issue:
        Some(_) => "in_progress"
        nil => "open"
```

**Logic:**
1. Has `[blocked:#123,#456]` → `"blocked"`
2. Has issue `[#789]` → `"in_progress"`
3. Otherwise → `"open"`

**Called from:** `convert_to_dashboard_todo()` at line 64

**When:** When dashboard collects TODO items for metrics

#### B. Rust Database Loader (Manual/Default)

**File:** `src/rust/driver/src/todo_db.rs`

**When loading from SDN (line 191):**
```rust
status: row_map.get("status").cloned().unwrap_or_else(|| "open".to_string())
```
- Reads `status` from SDN file
- Defaults to `"open"` if missing

**When creating new TODOs (line 501, 567):**
```rust
status: "open".to_string()
```

**When updating existing TODOs (line 545-554):**
```rust
if let Some(existing_record) = existing {
    // Update fields but NOT status
    existing_record.keyword = todo.keyword;
    existing_record.area = todo.area;
    existing_record.priority = normalized_priority;
    existing_record.description = todo.description;
    existing_record.issue = todo.issue;
    existing_record.blocked = todo.blocked;
    existing_record.valid = true;
    // NOTE: status is preserved from database!
    updated += 1;
}
```

**Important:** Status is **never updated** during rescanning - it persists from the database.

### Does Compiler Update TODO Status?

**Answer:** ❌ **NO**

The compiler does NOT update TODO status. The compiler only:
- Parses TODOs from source code
- Validates TODO format (via lint system)
- Extracts TODO metadata (area, priority, description, etc.)

### Does Lint System Update TODO Status?

**Answer:** ❌ **NO**

**File:** `src/rust/compiler/src/lint/checker.rs:502-584`

The lint checker function `check_todo_format()`:
- Reads source files
- Validates TODO/FIXME format
- Checks area and priority validity
- **Does NOT** update or track status
- **Does NOT** write to any database

**What the linter does:**
```rust
fn check_todo_format(&mut self, source_file: &std::path::Path) {
    // Read source
    // Check format with regex
    // Validate area and priority
    // Emit lint diagnostics if invalid
    // That's it - no status updates
}
```

Called from: `check_module()` at line 112

### TODO Status Values

| Status | Meaning | How Assigned |
|--------|---------|--------------|
| `open` | Not started | Default for new TODOs, or inferred (no issue/blockers) |
| `blocked` | Has blocking dependencies | Auto-inferred from `[blocked:#123]` |
| `in_progress` | Work has started | Auto-inferred from `[#456]` |
| `stale` | Old/outdated TODO | **Manual only** - never auto-assigned |

### TODO Status Data Flow

```
┌─────────────────┐
│  Source Code    │
│  TODO: [area]   │
│  [priority]     │
│  [#issue]       │
│  [blocked:#n]   │
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│  TodoParser     │
│  scan_directory │
└────────┬────────┘
         │
         ▼
┌─────────────────────────────────────────┐
│           TodoItem                      │
│  (keyword, area, priority,              │
│   description, issue, blocked)          │
└──────────┬──────────────┬───────────────┘
           │              │
      [Simple Path]  [Rust Path]
           │              │
           ▼              ▼
┌────────────────┐  ┌──────────┐
│infer_todo_     │  │status =  │
│status()        │  │"open"    │
└───────┬────────┘  └────┬─────┘
        │                │
        ▼                ▼
  "blocked" |      Always "open"
  "in_progress" |
  "open"
        │                │
        ▼                ▼
┌────────────────┐  ┌──────────┐
│Dashboard       │  │TodoRecord│
│TodoItem        │  │in DB     │
└────────────────┘  └──────────┘
```

### Manual Status Updates

To manually set TODO status to `"stale"` or override auto-inference:

1. Edit SDN file directly:
```sdn
[todos]
fields = [id, keyword, area, priority, description, file, line, status, ...]
[
  ["1", "TODO", "runtime", "P2", "old task", "file.rs", "42", "stale", ...]
]
```

2. Use custom tool that updates the database

## 2. Feature Status Updates

### Who Updates Feature Status?

**Answer:** The **test runner** updates feature status automatically after running tests.

### When Is Feature Status Updated?

**File:** `src/rust/driver/src/cli/test_runner/runner.rs:39`

**Function:** `run_tests()`

```rust
// Execute tests
let (mut results, mut total_passed, mut total_failed) =
    execute_test_files(&runner, &test_files, &options, quiet);

// Update feature database (line 39)
update_feature_database(&test_files, &mut results, &mut total_failed);
```

**When:** Immediately after test execution, before diagram generation

### How Feature Status Is Updated

**File:** `src/rust/driver/src/cli/test_runner/feature_db.rs:10-39`

```rust
pub fn update_feature_database(
    test_files: &[PathBuf],
    results: &mut Vec<TestFileResult>,
    total_failed: &mut usize
) {
    let feature_db_path = PathBuf::from("doc/features/feature_db.sdn");

    // Filter for spec files
    let sspec_files: Vec<PathBuf> = test_files
        .iter()
        .filter(|path| path.file_name()
            .and_then(|n| n.to_str())
            .map(|n| n.ends_with("_spec.spl"))
            .unwrap_or(false))
        .cloned()
        .collect();

    // Identify failed specs
    let failed_specs: Vec<PathBuf> = results
        .iter()
        .filter(|result| result.failed > 0 || result.error.is_some())
        .map(|result| result.path.clone())
        .collect();

    // Update database
    if let Err(e) = crate::feature_db::update_feature_db_from_sspec(
        &feature_db_path,
        &sspec_files,
        &failed_specs
    ) {
        // Handle error...
    }
}
```

### Feature Status Update Logic

**File:** `src/rust/driver/src/feature_db.rs:290-326`

**Function:** `upsert_from_sspec()`

```rust
pub fn upsert_from_sspec(&mut self, item: &SspecItem, path: &Path, failed: bool) {
    let entry = self.records.entry(item.id.clone()).or_insert_with(|| {
        FeatureRecord {
            id: item.id.clone(),
            category: derived_category.clone().unwrap_or_else(|| "Uncategorized".to_string()),
            name: item.name.clone(),
            description: item.description.clone(),
            spec: path.display().to_string(),
            modes: ModeSupport::with_defaults(),
            platforms: item.platforms.clone(),
            status: "planned".to_string(),  // Default for new features
            valid: true,
        }
    });

    // Update fields from spec...

    // Update status based on test results
    if item.ignored {
        entry.status = "ignored".to_string();
    } else if failed {
        entry.status = "failed".to_string();
    } else if entry.status == "ignored" || entry.status == "failed" {
        entry.status = "planned".to_string();
    }
    // NOTE: If status is "complete" or "in_progress", it is NOT changed

    entry.valid = true;
}
```

### Feature Status Values

| Status | Meaning | How Assigned |
|--------|---------|--------------|
| `planned` | Feature exists but not implemented | Default for new features |
| `in_progress` | Implementation started | **Manual only** |
| `complete` | Fully implemented and tested | **Manual only** |
| `failed` | Tests are failing | Auto-assigned when tests fail |
| `ignored` | Test is marked with `#[ignore]` | Auto-assigned when test ignored |

### Feature Status Persistence Rules

When test runner updates features:

| Current Status | Test Passed | Test Failed | Test Ignored | New Status |
|----------------|-------------|-------------|--------------|------------|
| `planned` | ✓ | | | `planned` (unchanged) |
| `planned` | | ✓ | | `failed` |
| `planned` | | | ✓ | `ignored` |
| `in_progress` | ✓ | | | `in_progress` (unchanged) |
| `in_progress` | | ✓ | | `failed` |
| `in_progress` | | | ✓ | `ignored` |
| `complete` | ✓ | | | `complete` (unchanged) |
| `complete` | | ✓ | | `failed` |
| `complete` | | | ✓ | `ignored` |
| `failed` | ✓ | | | `planned` (recovered) |
| `ignored` | ✓ | | | `planned` (recovered) |

**Key Insight:** Status `"complete"` and `"in_progress"` are **preserved** unless the test fails or is ignored. You must manually set features to `"complete"` in the SDN file.

### Feature Database File

**Location:** `doc/feature/feature_db.sdn`

**Structure:**
```sdn
features |id, category, name, description, spec, mode_interpreter, mode_jit, mode_smf_cranelift, mode_smf_llvm, platforms, status, valid|
    1, Infrastructure, Lexer, "Tokenizes source code...", doc/spec/lexer_parser.md, supported, supported, supported, supported, , complete, true
    2, Infrastructure, Parser, "Transforms tokens...", doc/spec/lexer_parser.md, supported, supported, supported, supported, , complete, true
    ...
```

**Status Column:** Column 11 (1-indexed)

### Feature Status Update Flow

```
┌──────────────────┐
│ Run Tests        │
│ simple test      │
└────────┬─────────┘
         │
         ▼
┌──────────────────────┐
│ Execute Test Files   │
│ (test_runner.rs:36)  │
└────────┬─────────────┘
         │
         ▼
┌──────────────────────────────┐
│ Update Feature Database      │
│ (test_runner/runner.rs:39)   │
└────────┬─────────────────────┘
         │
         ▼
┌──────────────────────────────────┐
│ update_feature_database()        │
│ - Collect _spec.spl files        │
│ - Identify failed tests          │
│ (test_runner/feature_db.rs:10)   │
└────────┬─────────────────────────┘
         │
         ▼
┌──────────────────────────────────┐
│ update_feature_db_from_sspec()   │
│ - Load feature_db.sdn            │
│ - Parse SSpec files for features │
│ (feature_db.rs:243)              │
└────────┬─────────────────────────┘
         │
         ▼
┌──────────────────────────────────┐
│ upsert_from_sspec()              │
│ - Update/insert feature record   │
│ - Set status based on test result│
│ (feature_db.rs:290)              │
└────────┬─────────────────────────┘
         │
         ▼
┌──────────────────────────────────┐
│ save_feature_db()                │
│ - Write to feature_db.sdn        │
│ (feature_db.rs:274)              │
└──────────────────────────────────┘
```

## 3. Manual Status Updates

### Manually Setting Feature to "complete"

Since the test runner doesn't automatically mark features as `"complete"`, you must edit the SDN file:

```bash
# Edit doc/feature/feature_db.sdn
# Find the feature row by ID
# Change status column from "planned" to "complete"
```

Example:
```sdn
# Before
40, Concurrency, Actors, "Actor-based...", doc/spec/concurrency.md, supported, supported, supported, supported, , planned, true

# After
40, Concurrency, Actors, "Actor-based...", doc/spec/concurrency.md, supported, supported, supported, supported, , complete, true
```

### Tool for Bulk Status Updates

You could create a Simple script to bulk update feature status:

```simple
# Example: scripts/update_feature_status.spl
val db = load_feature_db("doc/feature/feature_db.sdn")

# Mark all passing tests as complete
for feature in db.records:
    if feature.status == "planned" and feature.all_tests_pass():
        feature.status = "complete"

save_feature_db("doc/feature/feature_db.sdn", db)
```

## 4. Key Differences

| Aspect | TODO Status | Feature Status |
|--------|-------------|----------------|
| **Updated by** | Simple collector (auto) | Test runner (auto) |
| **When** | Dashboard collection | After test execution |
| **Auto-inferred** | Yes (`blocked`, `in_progress`) | Partially (`failed`, `ignored`) |
| **Manual-only states** | `stale` | `complete`, `in_progress` |
| **Preserved on rescan** | Yes (Rust DB) | Yes (unless test fails) |
| **Database file** | None (or custom SDN) | `doc/feature/feature_db.sdn` |
| **Updated by compiler** | ❌ No | ❌ No |
| **Updated by linter** | ❌ No | ❌ No |

## 5. Related Files

### TODO Status
- `src/lib/std/src/tooling/dashboard/collectors/todo_collector.spl` - Status inference
- `src/rust/driver/src/todo_db.rs` - Database management
- `src/rust/driver/src/todo_parser.rs` - Parsing (no status)
- `src/rust/compiler/src/lint/checker.rs` - Format validation (no status)

### Feature Status
- `src/rust/driver/src/feature_db.rs` - Database management and updates
- `src/rust/driver/src/cli/test_runner/feature_db.rs` - Test integration
- `src/rust/driver/src/cli/test_runner/runner.rs` - Test execution trigger
- `doc/feature/feature_db.sdn` - Feature database file

## See Also

- `doc/report/todo_status_generation_2026-01-21.md` - Detailed TODO status generation
- `doc/report/todo_skip_attribute_implementation_2026-01-21.md` - Skip attribute for TODO checking
- `.claude/skills/todo.md` - TODO format specification
