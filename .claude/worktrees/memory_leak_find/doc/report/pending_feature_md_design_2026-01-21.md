# Pending Features Documentation Design

**Date:** 2026-01-21
**Feature:** Add `pending_feature.md` to track incomplete features
**Status:** Design proposal

## Overview

Add a `pending_feature.md` file that lists all features that are not yet complete, automatically generated during feature doc generation (every test run).

## Motivation

**Current state:**
- `feature.md` - Shows all features by category (complete + incomplete)
- `category/*.md` - Shows features grouped by category
- **Missing:** Quick view of what's left to implement

**Problem:**
- Hard to see at a glance what features need work
- Must scan through all categories to find pending items
- No prioritized list of incomplete features

**Solution:** `pending_feature.md` - One file showing all incomplete features grouped by status

## Feature Status Values

From `src/rust/driver/src/feature_db.rs`:

| Status | Meaning | Include in Pending? |
|--------|---------|---------------------|
| `complete` | Fully implemented and tested | ❌ No |
| `in_progress` | Implementation started | ✅ Yes (high priority) |
| `planned` | Feature exists but not implemented | ✅ Yes (medium priority) |
| `failed` | Tests are failing | ✅ Yes (critical - needs fix) |
| `ignored` | Test marked with `#[ignore]` | ⚠️ Maybe (separate section) |

## Proposed File Structure

### File Location
`doc/feature/pending_feature.md`

### Content Structure

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

**Completion:** 85.2% (612 complete / 654 total)

---

## 🔴 Failed Features (3)

Features with failing tests - **needs immediate attention**

| ID | Category | Feature | Spec | Failure Reason |
|----|----------|---------|------|----------------|
| 97 | Codegen | LLVM Backend | [spec](../spec/codegen_technical.md) | Build errors |
| 234 | Network | WebSocket Client | [spec](../spec/network.md) | Connection timeout |
| 456 | ML | Tensor Slicing | [spec](../spec/ml.md) | Index out of bounds |

---

## 🟡 In Progress Features (12)

Features currently being implemented

### Infrastructure (2)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| 101 | Native Binary Compilation | Standalone binary generation with mold/lld linkers | [spec](../spec/binary_locality.md) |
| 245 | Hot Reload | Live code reloading for development | [spec](../spec/hot_reload.md) |

### Concurrency (3)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| 40 | Actors | Actor-based concurrency with spawn | [spec](../spec/concurrency.md) |
| 44 | Async Default | Functions async by default | [spec](../spec/async_default.md) |
| 45 | Suspension Operator (~) | Explicit suspension points | [spec](../spec/suspension_operator.md) |

[... more categories ...]

---

## 🟢 Planned Features (27)

Features specified but not yet implemented

### Language (5)

| ID | Feature | Description | Spec |
|----|---------|-------------|------|
| 123 | Union Types | Type-safe unions with pattern matching | [spec](../spec/types.md) |
| 156 | Const Generics | Generic parameters with const values | [spec](../spec/generics.md) |

[... more categories ...]

---

## ⚪ Ignored Features (5)

Features with tests marked `#[ignore]`

| ID | Category | Feature | Spec | Reason |
|----|----------|---------|------|--------|
| 789 | GPU | Ray Tracing | [spec](../spec/gpu.md) | Requires GPU hardware |
| 890 | Platform | iOS Support | [spec](../spec/platform.md) | Platform-specific |

---

## Progress by Category

| Category | Total | Complete | Pending | % Complete |
|----------|-------|----------|---------|------------|
| Infrastructure | 9 | 7 | 2 | 77.8% |
| Types | 7 | 7 | 0 | 100% |
| Language | 15 | 10 | 5 | 66.7% |
| Concurrency | 8 | 4 | 4 | 50.0% |
| Codegen | 5 | 4 | 1 | 80.0% |
| Testing Framework | 25 | 25 | 0 | 100% |

---

## Implementation Priority

### Critical (Do First)
1. Fix failed features (3 features)
2. Complete in_progress features (12 features)

### High (Next Sprint)
3. Planned features with dependencies (estimated: 8 features)

### Medium (Backlog)
4. Remaining planned features (19 features)

### Low (Future)
5. Ignored features (5 features) - requires special setup
```

## Implementation

### File: `src/rust/driver/src/feature_db.rs`

**Modify `generate_feature_docs()`:**

```rust
pub fn generate_feature_docs(db: &FeatureDb, output_dir: &Path) -> Result<(), String> {
    let mut all_records: Vec<&FeatureRecord> = db.records.values().collect();
    all_records.sort_by(|a, b| compare_feature_id(&a.id, &b.id));
    let mut records: Vec<&FeatureRecord> = all_records.iter().copied().filter(|record| record.valid).collect();
    records.sort_by(|a, b| compare_feature_id(&a.id, &b.id));
    let last_id = all_records.last().map(|record| record.id.clone()).unwrap_or_default();

    generate_feature_index(output_dir, &records, &last_id)?;
    generate_category_docs(output_dir, &records)?;

    // ✅ NEW: Generate pending features doc
    generate_pending_features(output_dir, &records)?;

    Ok(())
}
```

**Add new function:**

```rust
fn generate_pending_features(output_dir: &Path, records: &[&FeatureRecord]) -> Result<(), String> {
    use std::collections::BTreeMap;

    // Separate features by status
    let mut failed: Vec<&FeatureRecord> = Vec::new();
    let mut in_progress: Vec<&FeatureRecord> = Vec::new();
    let mut planned: Vec<&FeatureRecord> = Vec::new();
    let mut ignored: Vec<&FeatureRecord> = Vec::new();
    let mut complete: Vec<&FeatureRecord> = Vec::new();

    for record in records {
        match record.status.as_str() {
            "failed" => failed.push(record),
            "in_progress" => in_progress.push(record),
            "planned" => planned.push(record),
            "ignored" => ignored.push(record),
            "complete" => complete.push(record),
            _ => planned.push(record), // Unknown status -> treat as planned
        }
    }

    let total_pending = failed.len() + in_progress.len() + planned.len() + ignored.len();
    let total_features = records.len();
    let completion_pct = if total_features > 0 {
        (complete.len() as f64 / total_features as f64 * 100.0)
    } else {
        0.0
    };

    let mut md = String::new();
    md.push_str("# Pending Features\n\n");
    md.push_str(&format!("**Generated:** {}\n", chrono::Local::now().format("%Y-%m-%d")));
    md.push_str(&format!("**Total Pending:** {} features\n\n", total_pending));

    // Summary table
    md.push_str("## Summary\n\n");
    md.push_str("| Status | Count | Priority |\n");
    md.push_str("|--------|-------|---------|\n");
    md.push_str(&format!("| Failed | {} | 🔴 Critical |\n", failed.len()));
    md.push_str(&format!("| In Progress | {} | 🟡 High |\n", in_progress.len()));
    md.push_str(&format!("| Planned | {} | 🟢 Medium |\n", planned.len()));
    md.push_str(&format!("| Ignored | {} | ⚪ Low |\n\n", ignored.len()));
    md.push_str(&format!("**Completion:** {:.1}% ({} complete / {} total)\n\n", completion_pct, complete.len(), total_features));
    md.push_str("---\n\n");

    // Failed features section
    if !failed.is_empty() {
        md.push_str(&format!("## 🔴 Failed Features ({})\n\n", failed.len()));
        md.push_str("Features with failing tests - **needs immediate attention**\n\n");
        md.push_str("| ID | Category | Feature | Spec |\n");
        md.push_str("|----|----------|---------|------|\n");
        for record in &failed {
            let spec_link = if !record.spec.is_empty() {
                format!("[spec]({})", record.spec)
            } else {
                "-".to_string()
            };
            md.push_str(&format!(
                "| {} | {} | {} | {} |\n",
                record.id, record.category, record.name, spec_link
            ));
        }
        md.push_str("\n---\n\n");
    }

    // In Progress features section (grouped by category)
    if !in_progress.is_empty() {
        md.push_str(&format!("## 🟡 In Progress Features ({})\n\n", in_progress.len()));
        md.push_str("Features currently being implemented\n\n");

        let grouped = group_by_category(&in_progress);
        for (category, features) in grouped {
            md.push_str(&format!("### {} ({})\n\n", category, features.len()));
            md.push_str("| ID | Feature | Description | Spec |\n");
            md.push_str("|----|---------|-------------|------|\n");
            for record in features {
                let spec_link = if !record.spec.is_empty() {
                    format!("[spec]({})", record.spec)
                } else {
                    "-".to_string()
                };
                md.push_str(&format!(
                    "| {} | {} | {} | {} |\n",
                    record.id, record.name, record.description, spec_link
                ));
            }
            md.push_str("\n");
        }
        md.push_str("---\n\n");
    }

    // Planned features section (grouped by category)
    if !planned.is_empty() {
        md.push_str(&format!("## 🟢 Planned Features ({})\n\n", planned.len()));
        md.push_str("Features specified but not yet implemented\n\n");

        let grouped = group_by_category(&planned);
        for (category, features) in grouped {
            md.push_str(&format!("### {} ({})\n\n", category, features.len()));
            md.push_str("| ID | Feature | Description | Spec |\n");
            md.push_str("|----|---------|-------------|------|\n");
            for record in features {
                let spec_link = if !record.spec.is_empty() {
                    format!("[spec]({})", record.spec)
                } else {
                    "-".to_string()
                };
                md.push_str(&format!(
                    "| {} | {} | {} | {} |\n",
                    record.id, record.name, record.description, spec_link
                ));
            }
            md.push_str("\n");
        }
        md.push_str("---\n\n");
    }

    // Ignored features section
    if !ignored.is_empty() {
        md.push_str(&format!("## ⚪ Ignored Features ({})\n\n", ignored.len()));
        md.push_str("Features with tests marked `#[ignore]`\n\n");
        md.push_str("| ID | Category | Feature | Spec |\n");
        md.push_str("|----|----------|---------|------|\n");
        for record in &ignored {
            let spec_link = if !record.spec.is_empty() {
                format!("[spec]({})", record.spec)
            } else {
                "-".to_string()
            };
            md.push_str(&format!(
                "| {} | {} | {} | {} |\n",
                record.id, record.category, record.name, spec_link
            ));
        }
        md.push_str("\n---\n\n");
    }

    // Progress by category
    md.push_str("## Progress by Category\n\n");
    md.push_str("| Category | Total | Complete | Pending | % Complete |\n");
    md.push_str("|----------|-------|----------|---------|------------|\n");

    let mut category_stats: BTreeMap<String, (usize, usize)> = BTreeMap::new();
    for record in records {
        let cat = if record.category.is_empty() {
            "Uncategorized".to_string()
        } else {
            record.category.clone()
        };
        let entry = category_stats.entry(cat).or_insert((0, 0));
        entry.0 += 1; // total
        if record.status == "complete" {
            entry.1 += 1; // complete
        }
    }

    for (category, (total, complete)) in category_stats {
        let pending = total - complete;
        let pct = if total > 0 {
            (complete as f64 / total as f64 * 100.0)
        } else {
            0.0
        };
        md.push_str(&format!(
            "| {} | {} | {} | {} | {:.1}% |\n",
            category, total, complete, pending, pct
        ));
    }

    md.push_str("\n---\n\n");

    // Implementation priority
    md.push_str("## Implementation Priority\n\n");
    md.push_str("### Critical (Do First)\n");
    if !failed.is_empty() {
        md.push_str(&format!("1. Fix failed features ({} features)\n", failed.len()));
    }
    if !in_progress.is_empty() {
        md.push_str(&format!("2. Complete in_progress features ({} features)\n", in_progress.len()));
    }
    md.push_str("\n### High (Next Sprint)\n");
    md.push_str("3. Planned features with dependencies\n");
    md.push_str("\n### Medium (Backlog)\n");
    if !planned.is_empty() {
        md.push_str(&format!("4. Remaining planned features ({} features)\n", planned.len()));
    }
    md.push_str("\n### Low (Future)\n");
    if !ignored.is_empty() {
        md.push_str(&format!("5. Ignored features ({} features) - requires special setup\n", ignored.len()));
    }

    let path = output_dir.join("pending_feature.md");
    fs::write(&path, md).map_err(|e| e.to_string())?;

    Ok(())
}

// Helper function to group features by category
fn group_by_category<'a>(features: &[&'a FeatureRecord]) -> BTreeMap<String, Vec<&'a FeatureRecord>> {
    let mut grouped: BTreeMap<String, Vec<&FeatureRecord>> = BTreeMap::new();
    for record in features {
        let cat = if record.category.is_empty() {
            "Uncategorized".to_string()
        } else {
            record.category.clone()
        };
        grouped.entry(cat).or_default().push(record);
    }
    grouped
}
```

## When Updated

**Trigger:** Every test run (same as `feature.md`)

**Generated files after `simple test`:**
```
doc/feature/
├── feature_db.sdn          ← Database (always)
├── feature.md              ← Category index (always)
├── pending_feature.md      ← NEW: Pending features (always)
└── category/
    ├── Infrastructure.md   ← Per-category docs (always)
    ├── Types.md
    └── ...
```

## Benefits

### 1. Quick Status Overview
- See at a glance what needs work
- Prioritized by status (failed → in_progress → planned)
- Completion percentage per category

### 2. Better Project Planning
- Know how many features are pending
- Identify bottlenecks (many in_progress, few complete)
- Track progress over time

### 3. Team Coordination
- Clear view of what's being worked on (in_progress)
- Identify what needs attention (failed)
- Plan next sprint (planned features)

### 4. Quality Tracking
- Failed features highlighted prominently
- Can't be ignored - regenerated every test run
- Immediate visibility of broken tests

## Example Output

After running `simple test`:

```bash
# Test run completes
# Feature database updated:
#   - 654 features total
#   - 612 complete (93.6%)
#   - 42 pending
#
# Generated docs:
#   - doc/feature/feature_db.sdn
#   - doc/feature/feature.md
#   - doc/feature/pending_feature.md  ← NEW
#   - doc/feature/category/*.md (8 files)
```

View pending features:
```bash
cat doc/feature/pending_feature.md

# Pending Features
#
# **Generated:** 2026-01-21
# **Total Pending:** 42 features
#
# ## Summary
#
# | Status | Count | Priority |
# |--------|-------|----------|
# | Failed | 3 | 🔴 Critical |
# | In Progress | 12 | 🟡 High |
# | Planned | 27 | 🟢 Medium |
# | Ignored | 5 | ⚪ Low |
#
# **Completion:** 93.6% (612 complete / 654 total)
# ...
```

## Implementation Checklist

- [ ] Add `generate_pending_features()` function to `feature_db.rs`
- [ ] Add `group_by_category()` helper function
- [ ] Call `generate_pending_features()` from `generate_feature_docs()`
- [ ] Add `chrono` dependency for date formatting (or use existing)
- [ ] Test with current feature database
- [ ] Verify file is generated on test run
- [ ] Update documentation
- [ ] Add to `.gitignore` if treating as generated file (optional)

## Alternative: Combined File

Instead of separate file, could add "Pending Features" section to `feature.md`:

**Pros:**
- One file to check
- Less file clutter

**Cons:**
- `feature.md` becomes very long
- Harder to quickly find pending items
- Mixes index (categories) with status (pending)

**Recommendation:** Keep as separate file for clarity

## Integration with TODO System

**Comparison:**

| System | Database | Doc | Pending List |
|--------|----------|-----|--------------|
| **TODO** | `doc/todo/todo_db.sdn` | `doc/TODO.md` | Included in TODO.md (by priority) |
| **Feature** | `doc/feature/feature_db.sdn` | `doc/feature/feature.md` | `doc/feature/pending_feature.md` (NEW) |

**Consistency:** Both systems would have pending/incomplete items clearly visible

## Summary

✅ **Yes, add `pending_feature.md`** with automatic generation

**Key points:**
1. Generated every test run (automatic)
2. Shows failed, in_progress, planned, ignored features
3. Grouped by category for easy navigation
4. Includes progress statistics
5. Priority-ordered (critical → high → medium → low)

**Implementation:** ~150 lines of code in `feature_db.rs`

**Files generated after implementation:**
- `doc/feature/pending_feature.md` (NEW)
- All existing files (unchanged)
