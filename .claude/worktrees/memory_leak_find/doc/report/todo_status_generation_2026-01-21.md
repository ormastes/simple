# TODO Status Generation - Implementation Details

**Date:** 2026-01-21
**Purpose:** Document where and how TODO status is generated in the codebase

## Overview

TODO status is generated in **two places** depending on which system is being used:

1. **Simple Language Collector** - Automatic inference based on metadata
2. **Rust Database Loader** - Manual status from SDN file or defaults to "open"

## Status Values

| Status | Meaning | When Assigned |
|--------|---------|---------------|
| `open` | Not started, no blockers | Default for new TODOs |
| `blocked` | Has blocking dependencies | Auto-detected when `blocked` field present |
| `in_progress` | Work has started | Auto-detected when issue number present |
| `stale` | Old/outdated TODO | Manual only (not auto-detected) |

## 1. Simple Language Collector (Automatic Inference)

**Location:** `src/lib/std/src/tooling/dashboard/collectors/todo_collector.spl:86-94`

### Function: `infer_todo_status()`

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

### Logic

1. **Blocked:** If `blocked` list is not empty → `"blocked"`
2. **In Progress:** If has issue number (`#123`) → `"in_progress"`
3. **Open:** Otherwise → `"open"`

### Called From

`convert_to_dashboard_todo()` at line 64:
```simple
# Determine status
val status = infer_todo_status(parser_todo)
```

This is used when collecting TODOs for the dashboard system.

## 2. Rust Database Loader

**Location:** `src/rust/driver/src/todo_db.rs`

### When Loading from SDN File (Line 191)

```rust
status: row_map.get("status").cloned().unwrap_or_else(|| "open".to_string()),
```

- Reads `status` field from SDN file
- Defaults to `"open"` if not present
- **Preserves manual status assignments** from SDN file

### When Creating New Records (Line 501, 567)

```rust
status: "open".to_string(),
```

- All new TODOs start with `"open"` status
- No automatic inference in Rust code

### Status Update on Scan

**Location:** `src/rust/driver/src/todo_db.rs:545-554`

When updating existing TODOs during scan:
```rust
if let Some(existing_record) = existing {
    // Update existing record
    existing_record.keyword = todo.keyword;
    existing_record.area = todo.area;
    existing_record.priority = normalized_priority;
    existing_record.description = todo.description;
    existing_record.issue = todo.issue;
    existing_record.blocked = todo.blocked;
    existing_record.valid = true;
    // NOTE: status is NOT updated - preserved from database
    updated += 1;
}
```

**Important:** The `status` field is **NOT updated** during rescanning. Once set (either manually in SDN or initially to "open"), it persists.

## 3. Manual Status Management

The `"stale"` status is **never automatically assigned**. It must be:

1. **Manually edited** in the SDN database file:
   ```sdn
   [todos]
   fields = [id, keyword, area, priority, description, file, line, status, ...]
   [
     ["1", "TODO", "runtime", "P2", "old task", "file.rs", "42", "stale", ...]
   ]
   ```

2. **Or set through a custom tool** that updates the database

## Data Flow

### New TODO Discovery

```
Source Code
    ↓
TodoParser.scan_directory()
    ↓
TodoItem (keyword, area, priority, description, issue, blocked)
    ↓
[Simple Path]                          [Rust Path]
infer_todo_status()                    status = "open"
    ↓                                      ↓
"blocked" | "in_progress" | "open"    Always "open"
    ↓                                      ↓
Dashboard TodoItem                     TodoRecord in DB
```

### Existing TODO Update

```
Source Code
    ↓
TodoParser.scan_directory()
    ↓
Find existing record in DB
    ↓
Update fields (keyword, area, priority, description, issue, blocked)
    ↓
KEEP existing status (no change)
```

## Status Usage

### In Report Generation (`todo_db.rs:590-660`)

```rust
let open = db.count_by_status("open");
let blocked = db.count_by_status("blocked");
let stale = db.count_by_status("stale");

// Statistics by priority
let priority_open = records.iter()
    .filter(|r| r.priority == *priority && r.status == "open")
    .count();
let priority_blocked = records.iter()
    .filter(|r| r.priority == *priority && r.status == "blocked")
    .count();
let priority_stale = records.iter()
    .filter(|r| r.priority == *priority && r.status == "stale")
    .count();
```

### In Sections (`todo_db.rs:704-711`)

```rust
// Stale TODOs
let stale_todos: Vec<_> = records.iter()
    .filter(|r| r.status == "stale")
    .collect();
if !stale_todos.is_empty() {
    md.push_str("\n## Stale TODOs\n\n");
    // ... generate section
}
```

## Implementation Discrepancy

⚠️ **Important:** There's a discrepancy between the two systems:

| System | Status Inference | Preserves Manual Status |
|--------|------------------|-------------------------|
| Simple Collector | ✅ Automatic (`blocked`, `in_progress`) | ❌ Recalculated every time |
| Rust DB | ❌ Always "open" for new | ✅ Preserves from SDN |

### Recommendation

To get consistent status handling:

1. **Use Simple Collector** for dashboard (already does automatic inference)
2. **Extend Rust code** to also call `infer_todo_status()` logic:

```rust
fn infer_status(todo: &TodoItem) -> String {
    if !todo.blocked.is_empty() {
        return "blocked".to_string();
    }
    if todo.issue.is_some() {
        return "in_progress".to_string();
    }
    "open".to_string()
}

// In new record creation:
status: infer_status(&todo),
```

## Related Files

- `src/lib/std/src/tooling/dashboard/collectors/todo_collector.spl` - Simple collector with status inference
- `src/rust/driver/src/todo_db.rs` - Rust database management
- `src/rust/driver/src/todo_parser.rs` - TODO parsing (no status logic)
- `src/lib/std/src/tooling/dashboard/types.spl` - TodoItem type definition

## See Also

- `.claude/skills/todo.md` - TODO format specification
- `doc/report/todo_skip_attribute_implementation_2026-01-21.md` - Skip attribute implementation
