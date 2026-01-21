# TODO Skip Attribute Implementation

**Date:** 2026-01-21
**Status:** ✅ Complete
**Feature:** File-level `#![skip_todo]` attribute to exclude files from TODO format checking

## Problem

TODO parsing and lint checking created false positives in files that:
1. **Implement TODO parsers/collectors** - Contain TODO format strings and examples
2. **Process TODOs** - Migration scripts that manipulate TODO comments
3. **Document TODO format** - Examples of correct/incorrect formats
4. **Test TODO functionality** - Test cases with deliberately malformed TODOs

**Examples of noisy files:**
- `src/rust/driver/src/todo_parser.rs` - Parser implementation with format examples
- `src/lib/std/src/tooling/todo_parser.spl` - Simple TODO parser
- `src/lib/std/src/tooling/dashboard/collectors/todo_collector.spl` - Dashboard collector
- `scripts/simple/migrate_todo.spl` - Migration script
- `src/rust/compiler/src/lint/checker.rs` - Lint checking implementation
- `src/rust/compiler/src/lint/types.rs` - Lint type definitions with examples

## Solution

Implemented file-level skip attribute that works for both Rust and Simple files.

### Syntax

**Primary (Recommended):**
```rust
// Rust
//! #![skip_todo]
```

```simple
# Simple
# #![skip_todo]
```

**Alternative (Lint Consistency):**
```rust
//! #![allow(todo_format)]
```

```simple
# #![allow(todo_format)]
```

**Comment-based:**
```rust
// skip_todo
```

```simple
# skip_todo
```

### Implementation Details

#### 1. TODO Parser (`src/rust/driver/src/todo_parser.rs`)

Added `has_file_level_skip()` helper function:

```rust
/// Check if file has #![skip_todo] at the top
fn has_file_level_skip(content: &str) -> bool {
    // Check first 20 lines for skip markers
    for line in content.lines().take(20) {
        let trimmed = line.trim();
        // Primary pattern: #![skip_todo]
        if trimmed.contains("#![skip_todo]") {
            return true;
        }
        // Also support: #![allow(todo_format)] for lint consistency
        if trimmed.contains("#![allow(todo_format)]") {
            return true;
        }
        // Comment-based alternatives
        if trimmed.contains("skip_todo") && (trimmed.starts_with("//") || trimmed.starts_with('#')) {
            return true;
        }
    }
    false
}
```

Integrated into `parse_rust()` and `parse_simple()`:
```rust
fn parse_rust(&self, content: &str, path: &Path) -> Result<ParseResult, String> {
    let mut todos = Vec::new();
    let mut errors = Vec::new();

    // Check for file-level skip attribute
    if Self::has_file_level_skip(content) {
        return Ok(ParseResult { todos, errors });
    }
    // ... rest of parsing
}
```

#### 2. Lint Checker (`src/rust/compiler/src/lint/checker.rs`)

Added identical `has_file_level_skip_todo_format()` helper:

```rust
/// Check if file has #![skip_todo] at the top
fn has_file_level_skip_todo_format(content: &str) -> bool {
    // Same implementation as todo_parser.rs
}
```

Integrated into `check_todo_format()`:
```rust
fn check_todo_format(&mut self, source_file: &std::path::Path) {
    let source = match std::fs::read_to_string(source_file) {
        Ok(s) => s,
        Err(_) => return,
    };

    // Check for file-level skip attribute
    if Self::has_file_level_skip_todo_format(&source) {
        return;
    }
    // ... rest of checking
}
```

### Design Decisions

1. **Text-Based Detection** - Since TODO checking is text-based (not AST-based), the skip marker is detected via simple string matching in the first 20 lines

2. **Multiple Syntax Support** - Supports both `#![skip_todo]` (clearer) and `#![allow(todo_format)]` (lint-consistent) for flexibility

3. **Early Return** - Returns empty results immediately when skip marker is found, avoiding unnecessary parsing

4. **Language Agnostic** - Same syntax works for both Rust (`//`) and Simple (`#`) comments

5. **Top-of-File Placement** - Checks only first 20 lines to ensure skip marker is visible and intentional

## Testing

### Test 1: File with skip_todo attribute

```bash
$ cat /tmp/test_skip_todo.spl
# Test file for skip_todo attribute
# #![skip_todo]

# TODO: this should be skipped
# FIXME: this too should be skipped

fn test():
    print "testing skip_todo"
```

```bash
$ ./target/debug/simple lint /tmp/test_skip_todo.spl
/tmp/test_skip_todo.spl: OK
```

✅ **Pass** - No lint errors despite malformed TODOs

### Test 2: Real project file with skip_todo

File: `src/lib/std/src/tooling/dashboard/collectors/todo_collector.spl`

Contains: `# TODO: Extract from TODO comment or git blame` (line 81)

```bash
$ ./target/debug/simple lint src/lib/std/src/tooling/dashboard/collectors/todo_collector.spl
src/lib/std/src/tooling/dashboard/collectors/todo_collector.spl: OK
```

✅ **Pass** - Skips TODO checking for collector implementation

### Test 3: Build Verification

```bash
$ cargo build --bin simple
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 27.55s
```

✅ **Pass** - All changes compile successfully

## Files Modified

### Implementation
1. `src/rust/driver/src/todo_parser.rs` (+21 lines)
   - Added `has_file_level_skip()` function
   - Modified `parse_rust()` and `parse_simple()` to check for skip marker

2. `src/rust/compiler/src/lint/checker.rs` (+21 lines)
   - Added `has_file_level_skip_todo_format()` function
   - Modified `check_todo_format()` to check for skip marker

### Markers Added (7 files)
1. `src/rust/driver/src/todo_parser.rs` - Added `//! #![skip_todo]`
2. `src/rust/compiler/src/lint/checker.rs` - Added `//! #![skip_todo]`
3. `src/rust/compiler/src/lint/types.rs` - Added `//! #![skip_todo]`
4. `src/rust/compiler/src/lint/mod.rs` - Added `//! #![skip_todo]`
5. `src/lib/std/src/tooling/todo_parser.spl` - Added `# #![skip_todo]`
6. `src/lib/std/src/tooling/dashboard/collectors/todo_collector.spl` - Added `# #![skip_todo]`
7. `scripts/simple/migrate_todo.spl` - Added `# #![skip_todo]`

### Documentation
1. `.claude/skills/todo.md` (+44 lines)
   - Added "Skipping TODO Checks" section
   - Documented all supported syntaxes
   - Listed files using skip_todo

## Impact

### Before
- TODO parsers/collectors triggered their own lint warnings
- Documentation with examples flagged as violations
- Migration scripts reported false positives
- ~7 noisy files requiring manual filtering

### After
- Clean separation between "real" TODOs and meta-references
- Documentation can show examples freely
- Tools can process TODOs without being flagged
- Zero false positives from tool files

## Future Enhancements

1. **Block/Function-Level Skip** - Could extend to support function-level skipping:
   ```simple
   #[skip_todo]
   fn process_todo_comment(line: String):
       # TODO: can contain unformatted TODOs here
   ```

2. **Lint Configuration** - Add to project-wide lint config:
   ```toml
   [lints.todo_format]
   skip_patterns = ["**/test/**", "**/examples/**"]
   ```

3. **Auto-Detection** - Automatically skip files with specific patterns:
   - Files matching `*_parser.spl`, `*_collector.spl`
   - Directories: `doc/`, `examples/`, `scripts/`

4. **Validation Warning** - Warn if skip_todo is used inappropriately:
   ```
   Warning: #![skip_todo] found but file contains no TODO/FIXME. Remove skip marker?
   ```

## See Also

- `.claude/skills/todo.md` - TODO format specification
- `doc/report/todo_fixme_analysis_2026-01-21.md` - Analysis of all TODOs
- `src/rust/driver/src/todo_parser.rs` - Parser implementation
- `src/rust/compiler/src/lint/checker.rs` - Lint checker implementation
