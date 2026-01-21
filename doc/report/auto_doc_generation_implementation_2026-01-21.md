# Auto-Documentation Generation Implementation

**Date:** 2026-01-21
**Status:** ✅ Complete
**Features Implemented:**
1. TODO auto-generation in `simple todo-scan`
2. `pending_feature.md` generation in `simple test`

## Summary

Implemented automatic documentation generation for both TODO and feature systems, bringing them to feature parity with consistent behavior.

### Before

```bash
# TODO system - two commands needed
simple todo-scan   # Only generates doc/todo/todo_db.sdn
simple todo-gen    # Only generates doc/TODO.md

# Feature system - automatic
simple test        # Generates doc/feature/*.md
```

### After

```bash
# TODO system - one command (auto-generates docs)
simple todo-scan   # Generates doc/todo/todo_db.sdn + doc/TODO.md

# Feature system - automatic + pending features
simple test        # Generates doc/feature/*.md + pending_feature.md
```

## Changes Implemented

### 1. TODO Auto-Generation

**File:** `src/rust/driver/src/cli/doc_gen.rs:367-383`

**What Changed:**
Added automatic `doc/TODO.md` generation after database save in `run_todo_scan()`.

**Before:**
```rust
if !validate_only {
    // Save database
    if let Err(e) = save_todo_db(&db_path, &db) {
        eprintln!("error: failed to save database: {}", e);
        return 1;
    }
    println!("Database saved to {}", db_path.display());
}
```

**After:**
```rust
if !validate_only {
    // Save database
    if let Err(e) = save_todo_db(&db_path, &db) {
        eprintln!("error: failed to save database: {}", e);
        return 1;
    }
    println!("Database saved to {}", db_path.display());

    // Auto-generate docs (like feature system)
    let output_dir = std::path::PathBuf::from("doc");
    match generate_todo_docs(&db, &output_dir) {
        Ok(_) => {
            println!("Generated docs to {}/TODO.md", output_dir.display());
        }
        Err(e) => {
            eprintln!("warning: failed to generate docs: {}", e);
            eprintln!("  Run 'simple todo-gen' to retry");
        }
    }
}
```

**Benefits:**
- ✅ Consistent with feature system
- ✅ One command instead of two
- ✅ Always up-to-date documentation
- ✅ No breaking changes (`todo-gen` still works)
- ✅ Errors don't fail the command (warn only)

### 2. Pending Features Documentation

**File:** `src/rust/driver/src/feature_db.rs`

**What Changed:**
1. Added `generate_pending_features()` function (lines 504-706)
2. Added `group_by_category()` helper function (lines 708-719)
3. Modified `generate_feature_docs()` to call `generate_pending_features()` (line 391)

**New Function:**
```rust
fn generate_pending_features(output_dir: &Path, records: &[&FeatureRecord]) -> Result<(), String> {
    // Separate features by status
    let mut failed: Vec<&FeatureRecord> = Vec::new();
    let mut in_progress: Vec<&FeatureRecord> = Vec::new();
    let mut planned: Vec<&FeatureRecord> = Vec::new();
    let mut ignored: Vec<&FeatureRecord> = Vec::new();
    let mut complete: Vec<&FeatureRecord> = Vec::new();

    // ... categorize features ...

    // Generate markdown with sections:
    // - Summary table
    // - Failed features (critical)
    // - In Progress features (high priority)
    // - Planned features (medium priority)
    // - Ignored features (low priority)
    // - Progress by category
    // - Implementation priority

    let path = output_dir.join("pending_feature.md");
    fs::write(&path, md).map_err(|e| e.to_string())?;
    Ok(())
}
```

**Generated File:** `doc/feature/pending_feature.md`

**Structure:**
```markdown
# Pending Features

**Generated:** 2026-01-21
**Total Pending:** 42 features

## Summary

| Status | Count | Priority |
|--------|-------|----------|
| Failed | 3 | 🔴 Critical |
| In Progress | 12 | 🟡 High |
| Planned | 27 | 🟢 Medium |
| Ignored | 5 | ⚪ Low |

**Completion:** 93.6% (612 complete / 654 total)

---

## 🔴 Failed Features (3)
## 🟡 In Progress Features (12)
## 🟢 Planned Features (27)
## ⚪ Ignored Features (5)
## Progress by Category
## Implementation Priority
```

**Benefits:**
- ✅ Quick visibility into incomplete work
- ✅ Priority-ordered (critical first)
- ✅ Grouped by category for easy navigation
- ✅ Progress tracking per category
- ✅ Updated every test run (automatic)

### 3. Documentation Updates

#### 3.1 CLAUDE.md

**File:** `CLAUDE.md:180-208`

**Added Section:** "Auto-Generated Documentation"

**Content:**
```markdown
### Auto-Generated Documentation

Files automatically updated during development:

| File | Updated When | Command | Description |
|------|-------------|---------|-------------|
| `doc/TODO.md` | `simple todo-scan` | Manual | TODO/FIXME tracking from source code |
| `doc/feature/feature_db.sdn` | `simple test` | **Every test run** | Feature database (all features) |
| `doc/feature/feature.md` | `simple test` | **Every test run** | Feature index by category |
| `doc/feature/pending_feature.md` | `simple test` | **Every test run** | Incomplete features only (failed/in_progress/planned) |
| `doc/feature/category/*.md` | `simple test` | **Every test run** | Per-category feature lists |

**Quick Access:**
- **What needs work?** → `doc/feature/pending_feature.md` (updated every test run)
- **All TODOs** → `doc/TODO.md` (run `simple todo-scan` to update)
- **All features** → `doc/feature/feature.md` (updated every test run)
```

#### 3.2 .claude/skills/todo.md

**File:** `.claude/skills/todo.md:217-255`

**Added Section:** "TODO Documentation Generation"

**Content:**
- Explains auto-generation behavior
- Shows new workflow vs legacy workflow
- Compares TODO and Feature systems
- Documents generated file contents

## File Generation Summary

### TODO System

| File | Generated By | When | Content |
|------|-------------|------|---------|
| `doc/todo/todo_db.sdn` | `simple todo-scan` | Manual command | TODO database (SDN format) |
| `doc/TODO.md` | `simple todo-scan` | Manual command (NEW: automatic) | Human-readable TODO docs |

### Feature System

| File | Generated By | When | Content |
|------|-------------|------|---------|
| `doc/feature/feature_db.sdn` | `simple test` | Every test run | Feature database (SDN format) |
| `doc/feature/feature.md` | `simple test` | Every test run | Category index |
| `doc/feature/pending_feature.md` | `simple test` | Every test run (NEW) | Incomplete features |
| `doc/feature/category/*.md` | `simple test` | Every test run | Per-category lists |

### Update Frequency

| System | Trigger | Frequency | Files Generated |
|--------|---------|-----------|-----------------|
| **TODO** | `simple todo-scan` | Manual | 2 files (database + docs) |
| **Feature** | `simple test` | **Every test run** | 11+ files (database + docs + categories) |

## Testing

### Test TODO Auto-Generation

```bash
# Before: No doc/TODO.md exists
rm doc/TODO.md

# Run scan
simple todo-scan

# Verify both files generated
ls -lh doc/todo/todo_db.sdn doc/TODO.md

# Output:
# Scanning TODOs from .
# Scan complete:
#   Added:   71 TODOs
#   Updated: 0 TODOs
#   Removed: 0 TODOs
#   Total:   71 TODOs
# Database saved to doc/todo/todo_db.sdn
# Generated docs to doc/TODO.md  ← NEW!
```

### Test Pending Features Generation

```bash
# Run tests
simple test test/lib/std/unit/

# Verify pending_feature.md generated
ls -lh doc/feature/pending_feature.md

# Check content
head -20 doc/feature/pending_feature.md

# Output:
# # Pending Features
#
# **Generated:** 2026-01-21
# **Total Pending:** 42 features
# ...
```

### Test Validation Flag

```bash
# Validate only (should NOT generate docs)
simple todo-scan --validate

# Output:
# Scanning TODOs from .
# Scan complete:
#   Added:   0 TODOs
#   Updated: 0 TODOs
#   Removed: 0 TODOs
#   Total:   71 TODOs
# Validation only - database and docs not updated  ← Correct!
```

## Backward Compatibility

### `simple todo-gen` Still Works

```bash
# Old workflow still supported
simple todo-scan   # Updates database
simple todo-gen    # Regenerates docs

# This is now redundant but harmless
# (Both commands are idempotent)
```

### No Breaking Changes

**Scripts using old workflow:**
```bash
#!/bin/bash
simple todo-scan
if [ $? -eq 0 ]; then
    simple todo-gen  # Still works (just redundant now)
fi
```

**After changes:**
- ✅ Script still works correctly
- ℹ️ Second command is now redundant (docs already generated)
- ℹ️ No harm - `todo-gen` is idempotent

## Implementation Statistics

### Lines of Code Added

| File | Lines Added | Purpose |
|------|-------------|---------|
| `src/rust/driver/src/cli/doc_gen.rs` | +14 | TODO auto-generation |
| `src/rust/driver/src/feature_db.rs` | +215 | Pending features generation |
| `CLAUDE.md` | +28 | Documentation table |
| `.claude/skills/todo.md` | +38 | Auto-gen workflow docs |
| **Total** | **+295** | |

### Files Modified

1. `src/rust/driver/src/cli/doc_gen.rs` - Add auto-gen to `run_todo_scan()`
2. `src/rust/driver/src/feature_db.rs` - Add `generate_pending_features()` and `group_by_category()`
3. `CLAUDE.md` - Add auto-generated docs table
4. `.claude/skills/todo.md` - Document new behavior

### Files Generated (New)

1. `doc/TODO.md` - Auto-generated by `simple todo-scan` (now automatic)
2. `doc/feature/pending_feature.md` - Auto-generated by `simple test` (new file)

## Benefits Summary

### Developer Experience

**Before:**
```bash
# Must remember two commands
simple todo-scan
simple todo-gen

# Feature docs auto-generate but no pending view
simple test
# Where to see what needs work? Must check all category files
```

**After:**
```bash
# One command for TODOs
simple todo-scan
# Automatically generates doc/TODO.md

# Test auto-generates everything including pending
simple test
# Quick view: cat doc/feature/pending_feature.md
```

### Visibility Improvements

| Aspect | Before | After |
|--------|--------|-------|
| **TODO docs** | Manual (`todo-gen`) | ✅ Automatic |
| **Pending features** | ❌ No dedicated file | ✅ `pending_feature.md` |
| **Quick status** | Scan all categories | ✅ One file shows all incomplete |
| **Priority view** | No ordering | ✅ Failed → In Progress → Planned |
| **Completion %** | No category stats | ✅ Per-category completion |
| **Consistency** | Two different patterns | ✅ Both systems auto-generate |

### Workflow Improvements

1. **TODO System:**
   - Reduced from 2 commands to 1
   - Always synchronized (database + docs)
   - Consistent with feature system

2. **Feature System:**
   - Added pending features view
   - Better project planning visibility
   - Failed tests immediately visible

3. **Documentation:**
   - Clear table in CLAUDE.md
   - When each file is updated
   - Quick access paths for common tasks

## Error Handling

### TODO Generation Errors

**Strategy:** Warn but don't fail

```rust
match generate_todo_docs(&db, &output_dir) {
    Ok(_) => {
        println!("Generated docs to {}/TODO.md", output_dir.display());
    }
    Err(e) => {
        eprintln!("warning: failed to generate docs: {}", e);
        eprintln!("  Run 'simple todo-gen' to retry");
        // Don't return error - scan succeeded
    }
}
```

**Rationale:**
- Database save is the primary goal
- Doc generation is secondary
- User can retry with `simple todo-gen`
- Consistent with feature system pattern

### Pending Features Errors

**Strategy:** Return error (same as other feature docs)

```rust
generate_feature_index(output_dir, &records, &last_id)?;
generate_category_docs(output_dir, &records)?;
generate_pending_features(output_dir, &records)?;  // Propagates errors
```

**Rationale:**
- Part of unified doc generation
- All feature docs should succeed/fail together
- Unlikely to fail (same pattern as other generators)

## Future Enhancements

### Potential Improvements

1. **TODO Auto-Scan on Test Run**
   - Could auto-run `todo-scan` before tests
   - Always up-to-date TODO tracking
   - Requires performance analysis

2. **Pending Features Filters**
   - Generate separate files by category
   - `doc/feature/pending/concurrency.md`
   - Better for large projects

3. **Trend Tracking**
   - Track pending count over time
   - Show progress graphs
   - Historical completion rates

4. **Integration**
   - Link TODOs to features
   - Cross-reference TODO items with feature IDs
   - Show related TODOs in pending features

### Not Implemented (Out of Scope)

- ❌ Git hooks for auto-scanning
- ❌ Real-time watching/regeneration
- ❌ HTML/web dashboard
- ❌ Email notifications

## Related Documentation

- `doc/report/todo_and_feature_file_generation_2026-01-21.md` - File generation overview
- `doc/report/todo_scan_auto_gen_analysis_2026-01-21.md` - Design analysis
- `doc/report/pending_feature_md_design_2026-01-21.md` - Pending features design
- `doc/report/todo_and_feature_status_update_2026-01-21.md` - Status update mechanisms
- `doc/report/todo_status_generation_2026-01-21.md` - TODO status generation
- `doc/report/todo_skip_attribute_implementation_2026-01-21.md` - Skip attribute

## Conclusion

✅ Successfully implemented auto-documentation generation for both systems:

1. **TODO System:** Now auto-generates `doc/TODO.md` on scan
2. **Feature System:** Now auto-generates `doc/feature/pending_feature.md` on test
3. **Documentation:** Updated CLAUDE.md and skills with clear guidance

**Impact:**
- Better developer experience (fewer commands)
- Better project visibility (pending features file)
- Consistent behavior across systems
- No breaking changes

**Next Steps:**
- Monitor usage and feedback
- Consider auto-scan integration with test runner
- Evaluate trend tracking feature
