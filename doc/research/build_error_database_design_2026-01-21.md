# Build Error/Warning Database Design

**Date:** 2026-01-21
**Status:** Design Document
**Target:** Track build errors and warnings with automatic documentation generation

## Overview

Design a build error/warning tracking system that:
1. Records compilation errors and warnings per file
2. Limits to max 10 errors/warnings per file (prevent noise)
3. Stores error codes and location lists
4. Auto-generates `doc/build/recent_build.md` after each build

## Requirements

### Core Requirements

1. **Per-File Tracking:** Each file tracked separately
2. **Error/Warning Limit:** Max 10 errors + max 10 warnings per file
3. **Error Codes:** Store error codes (e.g., E0308, W1234)
4. **Locations:** Store file path, line, column for each error/warning
5. **Auto-Generation:** Generate `doc/build/recent_build.md` after each build
6. **Incremental Updates:** Track changes across builds

### Design Goals

- **Noise Reduction:** Limit per-file errors prevents overwhelming output
- **Actionable:** Show what needs fixing immediately
- **Historical:** Compare with previous builds
- **Integration:** Works with existing CI/CD workflows
- **Consistency:** Follows TODO/Feature/Test database patterns

## Database Schema

### Build Database (`doc/build/build_db.sdn`)

```sdn
{
  version: "1.0"
  last_updated: "2026-01-21T10:30:00Z"

  # Current build (most recent)
  current_build: {
    build_id: "build_20260121_103000"
    timestamp: "2026-01-21T10:30:00Z"
    build_type: "debug"           # debug, release, test
    command: "cargo build --workspace"

    # Overall summary
    summary: {
      total_files_compiled: 234
      files_with_errors: 3
      files_with_warnings: 12
      total_errors: 8
      total_warnings: 23
      build_status: "failed"      # success, failed, partial
      duration_ms: 4180
    }

    # Per-file errors and warnings
    files: [
      {
        file_path: "src/rust/compiler/src/hir/lower/expr/literals.rs"

        # Errors (max 10)
        errors: [
          {
            code: "E0308"
            message: "mismatched types: expected `i32`, found `u32`"
            location: {
              line: 234
              column: 12
              span: "12-15"        # Column range
            }
            severity: "error"
            help: "consider using `as i32` to cast"
          }
          {
            code: "E0425"
            message: "cannot find value `foo` in this scope"
            location: {
              line: 256
              column: 8
              span: "8-11"
            }
            severity: "error"
            help: null
          }
          # ... up to 10 errors
        ]

        # Warnings (max 10)
        warnings: [
          {
            code: "W0612"
            message: "unused variable: `bar`"
            location: {
              line: 145
              column: 9
              span: "9-12"
            }
            severity: "warning"
            help: "prefix with `_` to suppress this warning"
          }
          # ... up to 10 warnings
        ]

        # Truncation info (if more than 10)
        truncated: {
          errors: false             # True if >10 errors exist
          warnings: false           # True if >10 warnings exist
          additional_errors: 0      # Count of errors beyond 10
          additional_warnings: 0    # Count of warnings beyond 10
        }
      }
    ]
  }

  # Previous build (for comparison)
  previous_build: {
    build_id: "build_20260121_093000"
    timestamp: "2026-01-21T09:30:00Z"
    summary: {
      total_errors: 12
      total_warnings: 25
      build_status: "failed"
    }
    # Simplified - just summary for comparison
  }

  # Build history (last 10 builds)
  history: [
    {
      build_id: "build_20260121_103000"
      timestamp: "2026-01-21T10:30:00Z"
      total_errors: 8
      total_warnings: 23
      build_status: "failed"
      duration_ms: 4180
    }
    {
      build_id: "build_20260121_093000"
      timestamp: "2026-01-21T09:30:00Z"
      total_errors: 12
      total_warnings: 25
      build_status: "failed"
      duration_ms: 4350
    }
    # ... up to 10 builds
  ]

  # Configuration
  config: {
    max_errors_per_file: 10
    max_warnings_per_file: 10
    max_history_builds: 10
    auto_generate_docs: true
    doc_output_path: "doc/build/recent_build.md"
  }
}
```

## Generated Document: `doc/build/recent_build.md`

### Example Output

```markdown
# Recent Build Report

**Generated:** 2026-01-21 10:30:00
**Build ID:** build_20260121_103000
**Status:** ❌ FAILED
**Duration:** 4.18s

## Summary

| Metric | Count | Change |
|--------|-------|--------|
| Files Compiled | 234 | - |
| Files with Errors | 3 | 🟢 -1 |
| Files with Warnings | 12 | 🟢 -2 |
| Total Errors | 8 | 🟢 -4 |
| Total Warnings | 23 | 🟢 -2 |

## 🔴 Errors (8)

### src/rust/compiler/src/hir/lower/expr/literals.rs (2 errors)

**E0308:** mismatched types: expected `i32`, found `u32`
📍 `src/rust/compiler/src/hir/lower/expr/literals.rs:234:12`
```rust
    let x: i32 = value;  // value is u32
            ^
```
💡 **Help:** consider using `as i32` to cast

---

**E0425:** cannot find value `foo` in this scope
📍 `src/rust/compiler/src/hir/lower/expr/literals.rs:256:8`
```rust
    let y = foo;
        ^
```

---

### src/rust/parser/src/expressions/postfix.rs (3 errors)

**E0061:** this function takes 2 arguments but 3 were supplied
📍 `src/rust/parser/src/expressions/postfix.rs:89:5`

**E0277:** the trait `Clone` is not implemented for `Foo`
📍 `src/rust/parser/src/expressions/postfix.rs:102:15`

**E0308:** mismatched types: expected `Result<T, E>`, found `Option<T>`
📍 `src/rust/parser/src/expressions/postfix.rs:134:9`

---

### src/rust/type/src/checker_infer.rs (3 errors)

**E0599:** no method named `infer_type` found for type `TypeChecker`
📍 `src/rust/type/src/checker_infer.rs:456:21`

**E0382:** borrow of moved value: `ctx`
📍 `src/rust/type/src/checker_infer.rs:478:5`

**E0515:** cannot return reference to local variable `temp`
📍 `src/rust/type/src/checker_infer.rs:501:5`

---

## ⚠️ Warnings (23)

### Top Warning Files

| File | Warnings | Top Code |
|------|----------|----------|
| `src/rust/compiler/src/hir/lower/expr/literals.rs` | 5 | W0612 (unused variable) |
| `src/rust/parser/src/expressions/postfix.rs` | 4 | W0612 (unused variable) |
| `src/rust/type/src/checker_infer.rs` | 3 | W0419 (unused import) |
| `src/rust/runtime/src/monoio_runtime.rs` | 2 | W0612 (unused variable) |

<details>
<summary>Show all warnings (23)</summary>

### src/rust/compiler/src/hir/lower/expr/literals.rs (5 warnings)

**W0612:** unused variable: `bar`
📍 `src/rust/compiler/src/hir/lower/expr/literals.rs:145:9`
💡 **Help:** prefix with `_` to suppress this warning

**W0612:** unused variable: `temp`
📍 `src/rust/compiler/src/hir/lower/expr/literals.rs:167:13`

**W0419:** unused import: `HashMap`
📍 `src/rust/compiler/src/hir/lower/expr/literals.rs:12:5`

**W0612:** unused variable: `result`
📍 `src/rust/compiler/src/hir/lower/expr/literals.rs:201:9`

**W0612:** unused variable: `ctx`
📍 `src/rust/compiler/src/hir/lower/expr/literals.rs:289:9`

*(Showing 5 of 5 warnings)*

---

### src/rust/parser/src/expressions/postfix.rs (4 warnings)

**W0612:** unused variable: `node`
📍 `src/rust/parser/src/expressions/postfix.rs:67:9`

**W0612:** unused variable: `parser_state`
📍 `src/rust/parser/src/expressions/postfix.rs:89:9`

**W0419:** unused import: `Vec`
📍 `src/rust/parser/src/expressions/postfix.rs:8:17`

**W0612:** unused variable: `span`
📍 `src/rust/parser/src/expressions/postfix.rs:134:9`

*(Showing 4 of 4 warnings)*

---

### src/rust/type/src/checker_infer.rs (3 warnings)

**W0419:** unused import: `std::collections::HashMap`
📍 `src/rust/type/src/checker_infer.rs:5:5`

**W0612:** unused variable: `infer_ctx`
📍 `src/rust/type/src/checker_infer.rs:234:9`

**W0612:** unused variable: `env`
📍 `src/rust/type/src/checker_infer.rs:301:9`

*(Showing 3 of 3 warnings)*

</details>

---

## 📊 Build History (Last 10 Builds)

| Build ID | Time | Status | Errors | Warnings | Duration |
|----------|------|--------|--------|----------|----------|
| build_20260121_103000 | 10:30:00 | ❌ FAILED | 8 | 23 | 4.18s |
| build_20260121_093000 | 09:30:00 | ❌ FAILED | 12 | 25 | 4.35s |
| build_20260121_083000 | 08:30:00 | ❌ FAILED | 15 | 27 | 4.42s |
| build_20260120_163000 | 16:30:00 | ✅ SUCCESS | 0 | 18 | 3.98s |
| build_20260120_153000 | 15:30:00 | ✅ SUCCESS | 0 | 18 | 4.01s |

**Trend:** 🟢 Improving (errors: 15 → 8, warnings: 27 → 23)

---

## 🎯 Action Items

### Priority 1: Fix Errors (8)

1. **Fix type mismatches** (3 occurrences)
   - `src/rust/compiler/src/hir/lower/expr/literals.rs:234`
   - `src/rust/parser/src/expressions/postfix.rs:134`
   - Other locations...

2. **Fix undefined references** (2 occurrences)
   - `src/rust/compiler/src/hir/lower/expr/literals.rs:256`
   - `src/rust/type/src/checker_infer.rs:456`

3. **Fix borrow checker issues** (1 occurrence)
   - `src/rust/type/src/checker_infer.rs:478`

### Priority 2: Clean Warnings (23)

1. **Remove unused variables** (12 occurrences)
   - Consider using `_` prefix for intentionally unused variables
   - Or remove if truly unused

2. **Remove unused imports** (3 occurrences)
   - Run `cargo fix` to auto-remove

---

**Build Command:**
```bash
cargo build --workspace
```

**Previous Build:** build_20260121_093000 (09:30:00)
**Changes:** -4 errors, -2 warnings
```

## Implementation Design

### 1. Build Integration

**Hook into build process:**

```rust
// src/rust/driver/src/cli/build.rs

pub fn run_build(args: &[String]) -> i32 {
    let start = Instant::now();

    // Run cargo build and capture output
    let output = Command::new("cargo")
        .args(&["build", "--message-format=json"])
        .output()
        .expect("failed to execute cargo build");

    let duration_ms = start.elapsed().as_millis() as u64;

    // Parse build output
    let build_result = parse_build_output(&output.stdout);

    // Update build database
    update_build_db(&build_result, duration_ms);

    // Auto-generate docs
    if config.auto_generate_docs {
        generate_build_docs(&build_result);
    }

    if build_result.has_errors() {
        1  // Exit code for failed build
    } else {
        0  // Success
    }
}
```

### 2. Error Parsing

**Parse Cargo JSON output:**

```rust
// src/rust/driver/src/build_db.rs

use serde::{Deserialize, Serialize};

#[derive(Deserialize)]
struct CargoMessage {
    reason: String,
    message: Option<CompilerMessage>,
}

#[derive(Deserialize)]
struct CompilerMessage {
    code: Option<DiagnosticCode>,
    level: String,
    message: String,
    spans: Vec<DiagnosticSpan>,
}

#[derive(Deserialize)]
struct DiagnosticCode {
    code: String,  // "E0308", "unused_variables", etc.
}

#[derive(Deserialize)]
struct DiagnosticSpan {
    file_name: String,
    line_start: u32,
    line_end: u32,
    column_start: u32,
    column_end: u32,
    is_primary: bool,
}

fn parse_build_output(output: &[u8]) -> BuildResult {
    let mut errors_by_file: HashMap<String, Vec<BuildError>> = HashMap::new();
    let mut warnings_by_file: HashMap<String, Vec<BuildWarning>> = HashMap::new();

    for line in String::from_utf8_lossy(output).lines() {
        if let Ok(msg) = serde_json::from_str::<CargoMessage>(line) {
            if msg.reason == "compiler-message" {
                if let Some(compiler_msg) = msg.message {
                    let file = primary_span_file(&compiler_msg.spans);

                    match compiler_msg.level.as_str() {
                        "error" => {
                            let entry = errors_by_file.entry(file).or_insert_with(Vec::new);
                            if entry.len() < MAX_ERRORS_PER_FILE {
                                entry.push(parse_error(&compiler_msg));
                            }
                        }
                        "warning" => {
                            let entry = warnings_by_file.entry(file).or_insert_with(Vec::new);
                            if entry.len() < MAX_WARNINGS_PER_FILE {
                                entry.push(parse_warning(&compiler_msg));
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    BuildResult {
        errors_by_file,
        warnings_by_file,
    }
}
```

### 3. Database Update

**Update build database with new results:**

```rust
fn update_build_db(result: &BuildResult, duration_ms: u64) {
    let db_path = PathBuf::from("doc/build/build_db.sdn");

    // Load existing database
    let mut db = load_build_db(&db_path).unwrap_or_else(|_| BuildDb::new());

    // Move current to previous
    db.previous_build = db.current_build.take().map(|b| BuildSummary {
        build_id: b.build_id,
        timestamp: b.timestamp,
        total_errors: b.summary.total_errors,
        total_warnings: b.summary.total_warnings,
        build_status: b.summary.build_status,
    });

    // Create new current build
    db.current_build = Some(BuildRecord {
        build_id: format!("build_{}", now_formatted()),
        timestamp: now(),
        build_type: "debug",
        command: "cargo build --workspace",
        summary: compute_summary(result),
        files: result.to_file_records(),
    });

    // Update history (keep last 10)
    db.history.insert(0, db.current_build.as_ref().unwrap().to_summary());
    if db.history.len() > 10 {
        db.history.truncate(10);
    }

    // Save database
    save_build_db(&db_path, &db).expect("failed to save build db");
}
```

### 4. Documentation Generation

**Generate markdown report:**

```rust
fn generate_build_docs(db: &BuildDb) -> Result<(), String> {
    let output_path = PathBuf::from("doc/build/recent_build.md");

    let mut md = String::new();

    // Header
    md.push_str(&format!("# Recent Build Report\n\n"));
    md.push_str(&format!("**Generated:** {}\n", format_timestamp(&now())));

    let current = db.current_build.as_ref().ok_or("no current build")?;
    md.push_str(&format!("**Build ID:** {}\n", current.build_id));

    let status_emoji = match current.summary.build_status.as_str() {
        "success" => "✅ SUCCESS",
        "failed" => "❌ FAILED",
        _ => "⚠️ PARTIAL",
    };
    md.push_str(&format!("**Status:** {}\n", status_emoji));
    md.push_str(&format!("**Duration:** {:.2}s\n\n", current.summary.duration_ms as f64 / 1000.0));

    // Summary table
    generate_summary_table(&mut md, current, &db.previous_build);

    // Errors section
    if current.summary.total_errors > 0 {
        generate_errors_section(&mut md, &current.files);
    }

    // Warnings section
    if current.summary.total_warnings > 0 {
        generate_warnings_section(&mut md, &current.files);
    }

    // Build history
    generate_history_table(&mut md, &db.history);

    // Action items
    generate_action_items(&mut md, &current.files);

    // Write file
    fs::write(&output_path, md).map_err(|e| e.to_string())?;

    Ok(())
}
```

## CLI Commands

### Build Commands

```bash
# Build with error tracking
simple build [--release] [--workspace]

# Generate build report from existing database
simple build-report [--output=doc/build/recent_build.md]

# Show build history
simple build-history [--count=10]

# Compare two builds
simple build-compare <build_id_1> <build_id_2>

# Export build data
simple build-export --format=json --output=build_export.json
```

### Example Usage

```bash
# Build and auto-generate report
$ simple build --workspace
Compiling simple-parser v0.1.0
Compiling simple-compiler v0.1.0
error[E0308]: mismatched types
 --> src/rust/compiler/src/hir/lower/expr/literals.rs:234:12
  |
234 |     let x: i32 = value;
  |            ^^^   ^^^^^ expected `i32`, found `u32`

... (more errors)

Build failed with 8 errors, 23 warnings
Build database updated: doc/build/build_db.sdn
Generated report: doc/build/recent_build.md

# View report
$ cat doc/build/recent_build.md
(shows formatted markdown)

# Compare with previous build
$ simple build-compare build_20260121_093000 build_20260121_103000
Changes:
  Errors: 12 → 8 (-4) 🟢
  Warnings: 25 → 23 (-2) 🟢

New errors: 0
Fixed errors: 4
  - Fixed E0308 in src/rust/compiler/src/hir/lower/expr/literals.rs:145
  - Fixed E0425 in src/rust/parser/src/expressions/postfix.rs:67
  ...
```

## Integration with Existing Systems

### Consistency with TODO/Feature/Test Systems

| System | Command | Database | Generated Doc | Updated When |
|--------|---------|----------|---------------|--------------|
| **TODO** | `simple todo-scan` | `doc/todo/todo_db.sdn` | `doc/TODO.md` | Manual |
| **Feature** | `simple test` | `doc/feature/feature_db.sdn` | `doc/feature/*.md` | Every test run |
| **Test Timing** | `simple test` | `doc/test/test_db.sdn` | `doc/test/timing_report.md` | Every test run |
| **Build** | `simple build` | `doc/build/build_db.sdn` | `doc/build/recent_build.md` | **Every build** |

### Update CLAUDE.md

Add to auto-generated documentation table:

```markdown
### Auto-Generated Documentation

| File | Updated When | Command | Description |
|------|-------------|---------|-------------|
| `doc/TODO.md` | `simple todo-scan` | Manual | TODO/FIXME tracking |
| `doc/feature/pending_feature.md` | `simple test` | **Every test run** | Incomplete features |
| `doc/test/timing_report.md` | `simple test` | **Every test run** | Test timing analysis |
| `doc/build/recent_build.md` | `simple build` | **Every build** | Build errors and warnings |
```

## Advanced Features

### 1. Error Grouping

Group similar errors together:

```markdown
## 🔴 Errors by Type

### Type Mismatches (3 errors)
- E0308 in `literals.rs:234`
- E0308 in `postfix.rs:134`
- E0308 in `checker_infer.rs:456`

### Undefined References (2 errors)
- E0425 in `literals.rs:256`
- E0599 in `checker_infer.rs:456`
```

### 2. Trend Analysis

```markdown
## 📈 Error Trends (Last 10 Builds)

Type Mismatches: 5 → 4 → 3 → 3 🟢 Improving
Unused Variables: 15 → 14 → 12 → 12 🟢 Improving
Borrow Checker: 2 → 2 → 1 → 1 🟢 Stable
```

### 3. Fix Suggestions

```markdown
## 🔧 Quick Fixes

### Auto-fixable Warnings (12)
Run: `cargo fix --allow-dirty`

### Common Patterns
1. **Unused variables** - Add `_` prefix or remove
2. **Unused imports** - Remove or use `#[allow(unused_imports)]`
```

### 4. CI Integration

```yaml
# .github/workflows/build.yml
- name: Build and track errors
  run: |
    simple build --workspace
    if [ -f doc/build/recent_build.md ]; then
      cat doc/build/recent_build.md >> $GITHUB_STEP_SUMMARY
    fi
```

## Configuration

### Build Config (`build_config.sdn`)

```sdn
{
  version: "1.0"

  # Limits
  max_errors_per_file: 10
  max_warnings_per_file: 10
  max_history_builds: 10

  # Auto-generation
  auto_generate_docs: true
  doc_output_path: "doc/build/recent_build.md"

  # Report options
  report_options: {
    show_help_text: true
    show_code_snippets: true
    group_by_error_type: true
    show_trends: true
    collapse_warnings: true      # Use <details> for warnings
  }

  # CI integration
  ci_options: {
    fail_on_errors: true
    fail_on_warnings: false
    warning_threshold: 50        # Fail if warnings > 50
  }
}
```

## Implementation Phases

### Phase 1: Basic Error Tracking
1. Parse Cargo JSON output
2. Create `build_db.sdn` schema
3. Store errors/warnings (max 10 per file)
4. Basic CLI: `simple build`

### Phase 2: Documentation Generation
1. Implement `generate_build_docs()`
2. Generate `doc/build/recent_build.md`
3. Summary table and error listings
4. Warning collapsing

### Phase 3: History and Comparison
1. Track last 10 builds
2. Compare current vs previous
3. Trend indicators (🟢/🔴/🟡)
4. CLI: `simple build-history`, `simple build-compare`

### Phase 4: Advanced Features
1. Error grouping by type
2. Trend analysis
3. Auto-fix suggestions
4. CI integration helpers

### Phase 5: Integration
1. Update CLAUDE.md documentation
2. Add to CI/CD pipelines
3. Create user guide

## Example Database State

```sdn
# doc/build/build_db.sdn (simplified)

{
  version: "1.0"
  current_build: {
    build_id: "build_20260121_103000"
    summary: {
      total_errors: 8
      total_warnings: 23
      build_status: "failed"
    }
    files: [
      {
        file_path: "src/rust/compiler/src/hir/lower/expr/literals.rs"
        errors: [
          { code: "E0308", message: "mismatched types...", location: { line: 234, column: 12 } }
          { code: "E0425", message: "cannot find value...", location: { line: 256, column: 8 } }
        ]
        warnings: [
          { code: "W0612", message: "unused variable...", location: { line: 145, column: 9 } }
          { code: "W0612", message: "unused variable...", location: { line: 167, column: 13 } }
          { code: "W0419", message: "unused import...", location: { line: 12, column: 5 } }
          { code: "W0612", message: "unused variable...", location: { line: 201, column: 9 } }
          { code: "W0612", message: "unused variable...", location: { line: 289, column: 9 } }
        ]
        truncated: { errors: false, warnings: false }
      }
    ]
  }
  previous_build: {
    build_id: "build_20260121_093000"
    summary: {
      total_errors: 12
      total_warnings: 25
    }
  }
  history: [
    { build_id: "build_20260121_103000", total_errors: 8, total_warnings: 23 }
    { build_id: "build_20260121_093000", total_errors: 12, total_warnings: 25 }
    { build_id: "build_20260121_083000", total_errors: 15, total_warnings: 27 }
  ]
}
```

## Benefits

### Developer Experience

**Before:**
- Build fails, scroll through terminal output
- Hard to see what changed since last build
- Errors buried in noise
- No historical tracking

**After:**
- Auto-generated `recent_build.md` shows summary
- Comparison with previous build
- Max 10 errors/warnings per file (no noise)
- Build history tracking
- Actionable fix suggestions

### Project Management

**Before:**
- No visibility into build health over time
- Can't track if errors are increasing or decreasing
- Hard to prioritize fixes

**After:**
- Build history shows trends
- Error/warning counts tracked
- Easy to see if project is improving or regressing
- Automated reports for stakeholders

### CI/CD Integration

**Before:**
- Build logs are verbose and hard to parse
- No summary in GitHub Actions
- Can't easily compare builds

**After:**
- Markdown report included in CI summary
- Clear pass/fail indicators
- Trend analysis visible in CI

## Next Steps

1. **Implement Phase 1:** Basic error tracking and database
2. **Implement Phase 2:** Documentation generation
3. **Test with real builds:** Verify error parsing and limits work
4. **Add to CI:** Integrate with existing GitHub Actions
5. **Document:** Update CLAUDE.md and create user guide

---

**End of Design Document**
