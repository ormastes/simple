# TODO Database Management System - Implementation Plan

**Date:** 2026-01-19
**Status:** Planning
**Related:** Feature DB (`doc/feature/feature_db.sdn`), Task DB (`doc/task/task_db.sdn`)

## Executive Summary

This document proposes a TODO database management system similar to the existing feature and task database systems. The system will automatically extract TODO/FIXME comments from source code (both `.spl` and `.rs` files), store them in an SDN database, and generate a comprehensive `doc/TODO.md` file.

## 1. Investigation Results

### 1.1 Current Systems Status

✅ **Feature Database System** - Working correctly
- Database: `doc/feature/feature_db.sdn`
- Code: `src/driver/src/feature_db.rs`
- Auto-updates from SSpec test execution
- Generates `doc/feature/feature.md` and category files
- Command: `simple feature-gen`
- Status: **67 features tracked successfully**

✅ **Task Database System** - Working correctly
- Database: `doc/task/task_db.sdn`
- Code: `src/driver/src/task_db.rs`
- Manual management (no auto-update)
- Generates `doc/task/task.md`
- Command: `simple task-gen`
- Status: **7 tasks tracked successfully**

### 1.2 TODO Format Specification

The project has a well-defined TODO format (`.claude/skills/todo.md`):

```
TODO: [area][priority] description [#issue] [blocked:#issue,#issue]
FIXME: [area][priority] description [#issue] [blocked:#issue,#issue]
```

**Required components:**
- **Keyword:** `TODO:` or `FIXME:`
- **Area:** `[runtime]`, `[codegen]`, `[compiler]`, `[parser]`, `[type]`, `[stdlib]`, `[gpu]`, `[ui]`, `[test]`, `[driver]`, `[loader]`, `[pkg]`, `[doc]`
- **Priority:** `[P0]`/`[critical]`, `[P1]`/`[high]`, `[P2]`/`[medium]`, `[P3]`/`[low]`
- **Description:** Free text

**Optional components:**
- **Issue:** `[#number]`
- **Blocked:** `[blocked:#n,#m]`

**Examples:**
```rust
// TODO: [runtime][P0] Implement monoio TCP write [#234]
// TODO: [stdlib][critical] Fix memory leak [#567] [blocked:#123]
// FIXME: [parser][P2] Handle edge case in expression parsing
```

```simple
# TODO: [gpu][P1] Create Vector3 variant [#789] [blocked:#100]
# FIXME: [stdlib][P0] Incorrect return value [#890]
```

### 1.3 Current TODO Lint Implementation

**Lint:** `todo_format` (`src/compiler/src/lint/checker.rs:477`)

**Current behavior:**
- ✅ Validates TODO format for Simple (`.spl`) files
- ❌ Does NOT check Rust (`.rs`) files (lint only runs on Simple source)
- ✅ Validates area and priority fields
- ✅ Provides helpful error messages

**Issue identified:** The lint cannot check Rust files because it's part of the Simple compiler's lint framework, which only processes `.spl` files during compilation.

### 1.4 Current TODO Statistics

**Source code analysis:**
- **1,298** Rust (`.rs`) files in codebase
- **1,446** Simple (`.spl`) files in codebase
- **56** TODO/FIXME comments found in Rust files (from 6 files)
- **Unknown** count in Simple files (requires full scan)

**Distribution in Rust files:**
```
src/runtime/src/value/ffi/file_io/directory.rs: 1
src/runtime/src/value/ffi/contracts.rs: 1
src/compiler/src/lint/types.rs: 18 (mostly examples in docs)
src/compiler/src/lint/checker.rs: 9 (mostly in code)
src/compiler/src/lint/mod.rs: 26 (mostly in tests)
src/driver/src/cli/migrate_sspec.rs: 1
```

## 2. Proposed TODO Database System

### 2.1 Architecture Overview

```
┌─────────────────────────────────────────────────────────────┐
│                    TODO Database System                      │
└─────────────────────────────────────────────────────────────┘
                              │
                ┌─────────────┴─────────────┐
                │                           │
         ┌──────▼──────┐           ┌───────▼────────┐
         │  Extraction │           │   Generation   │
         │   (Scan)    │           │  (doc/TODO.md) │
         └──────┬──────┘           └───────▲────────┘
                │                           │
      ┌─────────┼─────────┐                │
      │         │         │                │
  ┌───▼───┐ ┌──▼──┐  ┌───▼────┐   ┌──────┴────────┐
  │ .spl  │ │ .rs │  │  .md   │   │ todo_db.sdn   │
  │ files │ │files│  │  files │   │   (SDN DB)    │
  └───────┘ └─────┘  └────────┘   └───────────────┘
```

### 2.2 Database Schema (SDN Format)

**File:** `doc/todo/todo_db.sdn`

**Schema:**
```sdn
todos |id, keyword, area, priority, description, file, line, issue, blocked, status, valid|
    1, TODO, runtime, P0, "Implement monoio TCP write", src/runtime/tcp.rs, 123, 234, "", open, true
    2, FIXME, stdlib, critical, "Fix memory leak", src/liblib/mem.rs, 456, 567, "123", open, true
    3, TODO, gpu, P1, "Create Vector3 variant", src/gpu/vector.rs, 789, 789, "100", blocked, true
    4, TODO, parser, P2, "Handle edge case", src/parser/expr.rs, 234, "", "", open, true
```

**Fields:**

| Field | Type | Required | Description | Example |
|-------|------|----------|-------------|---------|
| `id` | String | Yes | Unique auto-increment ID | `"1"`, `"2"` |
| `keyword` | String | Yes | TODO or FIXME | `"TODO"`, `"FIXME"` |
| `area` | String | Yes | Component area | `"runtime"`, `"codegen"` |
| `priority` | String | Yes | Priority level (normalized) | `"P0"`, `"P1"` (critical→P0, high→P1) |
| `description` | String | Yes | What needs to be done | `"Implement socket write"` |
| `file` | String | Yes | Relative path from repo root | `"src/runtime/tcp.rs"` |
| `line` | Int | Yes | Line number in file | `123` |
| `issue` | String | No | Related issue number (without #) | `"234"` |
| `blocked` | String | No | Comma-separated issue IDs | `"100,101"` |
| `status` | String | Yes | Current status | `"open"`, `"blocked"`, `"stale"`, `"done"` |
| `valid` | Bool | Yes | Whether entry is current | `true`, `false` |

**Status values:**
- `open` - Active TODO, needs work
- `blocked` - Waiting on dependencies
- `stale` - File/line changed, needs verification
- `done` - Implemented but not yet removed from code

### 2.3 Component Design

#### 2.3.1 Core Module: `src/driver/src/todo_db.rs`

**Responsibilities:**
1. Parse and validate TODO comments using regex
2. Load/save TODO database from/to SDN format
3. Scan source files and extract TODOs
4. Update database with new/changed TODOs
5. Mark missing TODOs as invalid/stale
6. Generate markdown documentation

**Key functions:**
```rust
pub struct TodoRecord {
    pub id: String,
    pub keyword: String,
    pub area: String,
    pub priority: String,
    pub description: String,
    pub file: String,
    pub line: usize,
    pub issue: Option<String>,
    pub blocked: Vec<String>,
    pub status: String,
    pub valid: bool,
}

pub struct TodoDb {
    pub records: BTreeMap<String, TodoRecord>,
    next_id: usize,
}

// Core operations
pub fn load_todo_db(path: &Path) -> Result<TodoDb, String>
pub fn save_todo_db(path: &Path, db: &TodoDb) -> Result<(), std::io::Error>
pub fn scan_todos_in_file(path: &Path) -> Result<Vec<TodoRecord>, String>
pub fn update_todo_db_from_scan(db: &mut TodoDb, scan_results: Vec<TodoRecord>)
pub fn generate_todo_docs(db: &TodoDb, output_dir: &Path) -> Result<(), String>
```

#### 2.3.2 TODO Parser

**Regex patterns:**

```rust
// Main pattern for both Rust and Simple comments
const TODO_PATTERN: &str = r"(TODO|FIXME):\s*\[([^\]]+)\]\[([^\]]+)\]\s*(.+?)(?:\s*\[#(\d+)\])?(?:\s*\[blocked:(#\d+(?:,#\d+)*)\])?$";

// File type detection
fn is_rust_file(path: &Path) -> bool {
    path.extension().map(|e| e == "rs").unwrap_or(false)
}

fn is_simple_file(path: &Path) -> bool {
    path.extension().map(|e| e == "spl").unwrap_or(false)
}

fn is_markdown_file(path: &Path) -> bool {
    path.extension().map(|e| e == "md").unwrap_or(false)
}
```

**Comment extraction:**
- Rust: Lines starting with `//` or `///`
- Simple: Lines starting with `#`
- Markdown: HTML comments `<!-- TODO: ... -->`

#### 2.3.3 CLI Commands

**Location:** `src/driver/src/cli/doc_gen.rs`

**New commands:**

1. **`simple todo-scan`** - Scan codebase and update database
   ```bash
   simple todo-scan                    # Scan all source files
   simple todo-scan --db <path>        # Custom database path
   simple todo-scan --path <dir>       # Scan specific directory
   simple todo-scan --validate         # Check format, don't update
   ```

2. **`simple todo-gen`** - Generate TODO.md from database
   ```bash
   simple todo-gen                     # Generate doc/TODO.md
   simple todo-gen --db <path>         # Custom database path
   simple todo-gen -o <output>         # Custom output path
   ```

3. **`simple todo-check`** - Validate TODO format in files
   ```bash
   simple todo-check src/              # Check all files in src/
   simple todo-check --fix             # Auto-fix simple issues
   ```

**Workflow integration:**
```bash
# Add to make check-full
make check-full:
    cargo fmt -- --check
    cargo clippy
    cargo test --workspace
    ./target/debug/simple todo-scan      # Scan and update
    ./target/debug/simple todo-gen       # Generate docs
    git diff --exit-code doc/TODO.md     # Verify no changes
```

### 2.4 Generated Documentation Format

**File:** `doc/TODO.md`

**Structure:**
```markdown
# TODO List

**Generated:** 2026-01-19
**Total:** 145 items | **Open:** 98 | **Blocked:** 12 | **Stale:** 5
**Database:** doc/todo/todo_db.sdn

## Statistics

### By Area

| Area | Count | P0 | P1 | P2 | P3 | Blocked |
|------|-------|----|----|----|----|---------|
| runtime | 23 | 3 | 8 | 10 | 2 | 2 |
| codegen | 18 | 1 | 5 | 9 | 3 | 1 |
| compiler | 15 | 0 | 4 | 8 | 3 | 0 |
| ...

### By Priority

| Priority | Count | Open | Blocked | Stale |
|----------|-------|------|---------|-------|
| P0 (critical) | 8 | 6 | 2 | 0 |
| P1 (high) | 34 | 28 | 5 | 1 |
| P2 (medium) | 67 | 52 | 4 | 11 |
| P3 (low) | 36 | 32 | 1 | 3 |

## P0 Critical TODOs

### runtime

- **#1** [runtime][P0] Implement monoio TCP write [#234]
  - File: `src/runtime/tcp.rs:123`
  - Status: open

- **#2** [runtime][P0] Fix memory barrier race [#567] [blocked:#123]
  - File: `src/runtime/barrier.rs:456`
  - Status: blocked
  - Blocked by: #123

### stdlib

- **#15** [stdlib][P0] Fix memory corruption [#567]
  - File: `src/liblib/mem.rs:789`
  - Status: open

## P1 High Priority TODOs

### codegen

- **#7** [codegen][P1] Track line numbers in HIR [#789]
  - File: `src/codegen/hir.rs:234`
  - Status: open

...

## Stale TODOs

These TODOs may have moved or been modified:

- **#45** [test][P2] Add integration test cases
  - File: `src/test/integration.rs:567` (line changed)
  - Status: stale

## Appendix

### Legend

- **P0/critical:** Blocking, fix immediately
- **P1/high:** Important, next sprint
- **P2/medium:** Should do, backlog
- **P3/low:** Nice to have, someday

### Areas

- `runtime` - GC, values, monoio, concurrency
- `codegen` - MIR, Cranelift, LLVM, Vulkan
- `compiler` - HIR, pipeline, interpreter
- `parser` - Lexer, AST, parsing
- `type` - Type checker, inference
- `stdlib` - Simple standard library
- `gpu` - GPU/SIMD/graphics
- `ui` - UI framework
- `test` - Test frameworks
- `driver` - CLI, tools
- `loader` - SMF loader
- `pkg` - Package manager
- `doc` - Documentation, specs, guides
```

### 2.5 Staleness Detection

**How it works:**
1. During scan, compute hash of TODO line content
2. Compare with stored hash in database
3. If hash differs, mark as `stale`
4. Manual review required to update/remove

**Use cases:**
- Code refactoring moves TODO to different line
- TODO description is modified manually
- File is deleted but TODO remains in database

**Database additions:**
```sdn
todos |..., content_hash, last_seen|
    1, ..., "abc123def", "2026-01-19"
```

## 3. Implementation Phases

### Phase 1: Core Infrastructure (Priority: High)

**Tasks:**
1. Create `src/driver/src/todo_db.rs` module
2. Implement `TodoRecord` and `TodoDb` structures
3. Implement SDN parsing/serialization
4. Add unit tests for core data structures

**Deliverables:**
- [ ] `todo_db.rs` module with load/save functions
- [ ] Unit tests for SDN parsing
- [ ] Documentation in module

**Estimated complexity:** Medium (similar to `task_db.rs`)

### Phase 2: TODO Extraction (Priority: High)

**Tasks:**
1. Implement regex-based TODO parser
2. Add file scanner for `.rs`, `.spl`, `.md` files
3. Handle multi-line TODOs
4. Validate TODO format
5. Add extraction tests

**Deliverables:**
- [ ] `scan_todos_in_file()` function
- [ ] Support for Rust/Simple/Markdown
- [ ] Format validation
- [ ] Unit tests for parser

**Estimated complexity:** Medium

### Phase 3: Database Update Logic (Priority: High)

**Tasks:**
1. Implement database update algorithm
2. Add staleness detection (hash-based)
3. Handle TODO removal detection
4. Implement ID assignment logic
5. Add integration tests

**Deliverables:**
- [ ] `update_todo_db_from_scan()` function
- [ ] Staleness detection
- [ ] Integration tests

**Estimated complexity:** Medium-High

### Phase 4: Documentation Generation (Priority: Medium)

**Tasks:**
1. Implement markdown generation
2. Add statistics calculations
3. Add grouping by area/priority
4. Format with proper tables and links
5. Add generation tests

**Deliverables:**
- [ ] `generate_todo_docs()` function
- [ ] `doc/TODO.md` template
- [ ] Tests for doc generation

**Estimated complexity:** Low-Medium

### Phase 5: CLI Integration (Priority: Medium)

**Tasks:**
1. Add `todo-scan` command
2. Add `todo-gen` command
3. Add `todo-check` command (optional)
4. Update help text
5. Add CLI tests

**Deliverables:**
- [ ] CLI commands in `doc_gen.rs`
- [ ] Help documentation
- [ ] Integration with `make check-full`

**Estimated complexity:** Low

### Phase 6: Workflow Integration (Priority: Low)

**Tasks:**
1. Add to `make check-full` target
2. Add to CI/CD pipeline (if exists)
3. Document workflow in `CONTRIBUTING.md`
4. Add pre-commit hook (optional)

**Deliverables:**
- [ ] Makefile updates
- [ ] Documentation updates
- [ ] CI integration

**Estimated complexity:** Low

### Phase 7: Extended Features (Priority: Low/Future)

**Optional enhancements:**
1. Web dashboard for TODO visualization
2. GitHub issue integration
3. TODO aging metrics (days since created)
4. Email notifications for P0 TODOs
5. Jupyter notebook integration

**Deliverables:**
- [ ] Web UI (optional)
- [ ] Issue sync (optional)
- [ ] Analytics (optional)

**Estimated complexity:** High

## 4. Technical Decisions

### 4.1 Why SDN Format?

**Pros:**
- Consistent with existing feature/task databases
- Human-readable and editable
- Version control friendly
- Easy to parse with existing `simple-sdn` crate
- Supports tables with typed columns

**Cons:**
- Requires custom parser (already exists)
- Not as widely supported as JSON/YAML

**Decision:** Use SDN to maintain consistency with existing systems.

### 4.2 Why Auto-scan vs Manual Management?

**Auto-scan advantages:**
- Always in sync with source code
- No manual maintenance overhead
- Catches forgotten TODOs
- Enables metrics and tracking

**Manual management advantages:**
- More control over database content
- Can add TODOs not in code
- Simpler implementation

**Decision:** Use auto-scan (like feature DB) for automation, but allow manual edits to database for status updates.

### 4.3 Priority Normalization

**Problem:** TODOs use both `P0-P3` and `critical/high/medium/low`

**Solution:** Normalize during database insertion:
```rust
fn normalize_priority(priority: &str) -> &str {
    match priority.to_lowercase().as_str() {
        "critical" => "P0",
        "high" => "P1",
        "medium" => "P2",
        "low" => "P3",
        p => p,  // Keep P0-P3 as-is
    }
}
```

**Display:** Show both in docs (e.g., "P0 (critical)")

### 4.4 Multi-file vs Single-file Scan

**Option A:** Scan all files every time
- Simple implementation
- Potentially slow on large codebases
- Always accurate

**Option B:** Incremental scan (track file mtimes)
- More complex
- Faster on repeated scans
- Requires additional metadata

**Decision:** Start with Option A (full scan), optimize to Option B if performance becomes an issue.

### 4.5 Lint Integration

**Question:** Should `todo_format` lint check Rust files?

**Current state:** Only checks `.spl` files (compiler limitation)

**Options:**
1. Keep lint for `.spl` only, use `todo-check` command for Rust
2. Extract lint logic to shared module, use in both compiler and CLI
3. Create separate Rust lint using `cargo-clippy` integration

**Recommendation:** Option 1 initially (simplest), move to Option 2 if needed.

## 5. Edge Cases and Considerations

### 5.1 Multi-line TODOs

**Example:**
```rust
// TODO: [runtime][P1] Implement dedicated runtime thread [#234]
//       Need message passing between main thread and monoio runtime.
//       See monoio_tcp.rs:251 for context.
```

**Handling:** Capture first line for database, store full text in `description` field.

### 5.2 TODOs in Generated Files

**Problem:** Generated files may contain TODOs that shouldn't be tracked.

**Solution:** Exclude patterns:
- `target/`
- `*/generated/*`
- Files with `@generated` marker

### 5.3 Duplicate TODOs

**Problem:** Same TODO appears in multiple files.

**Solution:** Each occurrence is a separate database entry (different file/line).

### 5.4 Invalid TODOs

**Problem:** TODOs that don't match format.

**Solution:**
- In `todo-scan`: Warn but continue
- In `todo-check`: Error and fail
- In lint: Emit lint diagnostic

### 5.5 Removed Code

**Problem:** Code with TODO is deleted.

**Solution:** Mark as `invalid` in database during next scan. Generate "Removed TODOs" section in docs.

## 6. Testing Strategy

### 6.1 Unit Tests

**Module:** `src/driver/src/todo_db.rs`

Tests:
- [ ] Parse valid TODO comments
- [ ] Reject invalid TODO comments
- [ ] Load/save SDN database
- [ ] Priority normalization
- [ ] Staleness detection
- [ ] Multi-line TODO handling

### 6.2 Integration Tests

**Module:** `src/driver/tests/todo_db_tests.rs`

Tests:
- [ ] Scan directory of test files
- [ ] Update database from scan
- [ ] Generate markdown documentation
- [ ] Handle file deletion
- [ ] Handle TODO modification

### 6.3 CLI Tests

**Module:** `src/driver/tests/cli_tests.rs`

Tests:
- [ ] `simple todo-scan` command
- [ ] `simple todo-gen` command
- [ ] `simple todo-check` command
- [ ] Error handling for invalid input

### 6.4 Test Data

**Location:** `src/driver/test_data/todos/`

Files:
- `valid_todos.rs` - Correctly formatted TODOs
- `invalid_todos.rs` - Invalid format TODOs
- `multiline_todos.spl` - Multi-line TODOs
- `expected_db.sdn` - Expected database output
- `expected_output.md` - Expected markdown output

## 7. Migration Plan

### 7.1 Initial Database Creation

**Steps:**
1. Run initial scan: `simple todo-scan`
2. Review generated `doc/todo/todo_db.sdn`
3. Manually fix any invalid TODOs in source code
4. Re-run scan to verify
5. Generate docs: `simple todo-gen`
6. Commit both database and generated docs

### 7.2 Existing TODOs

**Current state:** Mix of formatted and unformatted TODOs

**Migration:**
1. Use existing migration script: `scripts/simple/migrate_todo.spl` (if it exists)
2. Or create new Rust-based migration tool
3. Run on all `.rs` and `.spl` files
4. Verify changes before committing

### 7.3 Documentation Updates

**Files to update:**
- `CLAUDE.md` - Add TODO database info
- `CONTRIBUTING.md` - Document TODO workflow
- `.claude/skills/todo.md` - Update with database info
- `Makefile` - Add TODO commands

## 8. Success Criteria

**Phase 1-3 Success (MVP):**
- [x] `doc/todo/todo_db.sdn` created and maintained
- [x] `simple todo-scan` command works
- [x] Database updates automatically from source code
- [x] All TODOs follow format specification

**Phase 4-5 Success (Complete):**
- [x] `doc/TODO.md` generated and readable
- [x] Statistics and metrics available
- [x] CLI commands integrated and documented
- [x] Tests passing with >90% coverage

**Phase 6 Success (Production):**
- [x] Integrated into development workflow
- [x] CI/CD pipeline includes TODO validation
- [x] Team using system regularly
- [x] Stale TODOs detected and resolved

## 9. Timeline Estimate

| Phase | Complexity | Estimated Time | Dependencies |
|-------|-----------|----------------|--------------|
| Phase 1 | Medium | 2-3 hours | None |
| Phase 2 | Medium | 3-4 hours | Phase 1 |
| Phase 3 | Medium-High | 4-5 hours | Phase 1, 2 |
| Phase 4 | Low-Medium | 2-3 hours | Phase 3 |
| Phase 5 | Low | 1-2 hours | Phase 4 |
| Phase 6 | Low | 1 hour | Phase 5 |
| Phase 7 | High | Future work | All above |

**Total MVP (Phases 1-5):** 12-17 hours
**Full Implementation (Phases 1-6):** 13-18 hours

## 10. Open Questions

1. **Should TODOs in test files be tracked separately?**
   - Proposal: Add `test_only` field to indicate test TODOs

2. **Should TODOs in comments vs documentation be differentiated?**
   - Proposal: Add `context` field: `code`, `doc`, `test`

3. **How to handle TODOs in third-party dependencies?**
   - Proposal: Exclude `vendor/`, `external/` directories

4. **Should we track WHO created the TODO?**
   - Proposal: Add `author` field via git blame (optional)

5. **Should we integrate with GitHub Issues API?**
   - Proposal: Phase 7 feature, auto-create issues for P0 TODOs

## 11. Risks and Mitigations

| Risk | Impact | Mitigation |
|------|--------|------------|
| Large codebase scan is slow | Medium | Implement incremental scan, parallel processing |
| Database conflicts in git | Low | Use merge-friendly SDN format |
| Invalid TODOs break scan | Medium | Add error recovery, continue on errors |
| Stale detection false positives | Low | Manual review process, allow override |
| Team resistance to format | High | Provide migration tools, clear documentation |

## 12. Alternatives Considered

### 12.1 Use Existing Tools

**Options:**
- `cargo-fixme` - Rust-only, no custom format
- `leasot` - JavaScript, limited customization
- `todo-cli` - Generic, no database

**Why not:** None support the exact TODO format specification and SDN database integration needed.

### 12.2 GitHub Issues Only

**Pros:** Native integration, notifications, assignment
**Cons:** Not in source code, requires network, overkill for small TODOs

**Decision:** Use both - database for code TODOs, issues for larger work items.

### 12.3 Notion/Jira Integration

**Pros:** Project management features, tracking, reporting
**Cons:** External dependency, not version controlled, overhead

**Decision:** Keep it simple with local database, add integrations later if needed.

## 13. References

- Feature Database: `src/driver/src/feature_db.rs`
- Task Database: `src/driver/src/task_db.rs`
- TODO Skill: `.claude/skills/todo.md`
- TODO Lint: `src/compiler/src/lint/checker.rs:477`
- SDN Library: `simple-sdn` crate

## 14. Conclusion

This plan provides a comprehensive roadmap for implementing a TODO database management system that:

1. ✅ Maintains consistency with existing feature/task databases
2. ✅ Automates TODO tracking from source code
3. ✅ Enforces the established TODO format specification
4. ✅ Generates useful documentation and metrics
5. ✅ Integrates with existing development workflow
6. ✅ Provides a foundation for future enhancements

**Next Steps:**
1. Review and approve this plan
2. Create GitHub issue/task for implementation
3. Begin Phase 1 implementation
4. Iterate based on feedback

**Approval Required:** Yes
**Estimated Start:** After approval
**Target Completion:** Phases 1-5 within 2-3 development sessions
