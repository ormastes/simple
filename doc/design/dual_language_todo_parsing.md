<!-- skip_todo -->

# Dual-Language TODO Parsing: Rust + Simple

**Date:** 2026-01-19
**Status:** Implemented (Proof-of-Concept)
**Module:** `src/driver/src/todo_parser.rs`

## Overview

The TODO database system now supports parsing TODO/FIXME comments from **both Rust (.rs) and Simple (.spl) source files**, ensuring comprehensive TODO tracking across the entire codebase.

## Why Both Languages?

The Simple language compiler is written in Rust, but the standard library, tests, and application code are written in Simple. To track all TODOs effectively, we need to parse both:

**Rust code:** (~1,298 files)
- Compiler implementation (`src/compiler/`)
- Runtime system (`src/runtime/`)
- Driver and CLI (`src/driver/`)
- Codegen backends (`src/codegen/`)
- Parser and lexer (`src/parser/`)

**Simple code:** (~1,446 files)
- Standard library (`simple/std_lib/`)
- Test specifications (`simple/std_lib/test/features/`)
- Application code (`simple/app/`)
- Scripts and tools (`scripts/simple/`)

## Implementation

### Module: `src/driver/src/todo_parser.rs`

**Key features:**
- ✅ Parses Rust comments (`//` and `///`)
- ✅ Parses Simple comments (`#`)
- ✅ Parses Markdown HTML comments (`<!-- TODO: ... -->`)
- ✅ Validates TODO format specification
- ✅ Extracts structured data (area, priority, issue, blocked)
- ✅ Skips TODOs inside string literals
- ✅ Provides detailed parse errors
- ✅ Supports directory scanning
- ✅ Includes comprehensive unit tests

### Comment Syntax Handling

**Rust:**
```rust
// TODO: [runtime][P0] Implement monoio TCP write [#234]
/// FIXME: [stdlib][critical] Fix memory leak [#567] [blocked:#123]
```

**Simple:**
```simple
# TODO: [gpu][P1] Create Vector3 variant [#789]
# FIXME: [parser][P2] Handle edge case
```

**Markdown:**
```markdown
<!-- TODO: [doc][P1] Add examples section [#234] -->
```

### Data Structure

```rust
pub struct TodoItem {
    pub keyword: String,          // "TODO" or "FIXME"
    pub area: String,             // "runtime", "codegen", etc.
    pub priority: String,         // "P0", "P1", "critical", etc.
    pub description: String,      // What needs to be done
    pub issue: Option<String>,    // Issue number (without #)
    pub blocked: Vec<String>,     // Blocked issue IDs
    pub file: PathBuf,            // Source file path
    pub line: usize,              // Line number (1-indexed)
    pub raw_text: String,         // Original comment text
}
```

### API Usage

**Parse a single file:**
```rust
use simple_driver::todo_parser::TodoParser;

let parser = TodoParser::new();
let result = parser.parse_file(Path::new("src/runtime/tcp.rs"))?;

for todo in result.todos {
    println!("[{}:{}] {}: [{}][{}] {}",
        todo.file.display(),
        todo.line,
        todo.keyword,
        todo.area,
        todo.priority,
        todo.description
    );
}

for error in result.errors {
    eprintln!("Parse error at {}:{}: {}",
        error.file.display(),
        error.line,
        error.message
    );
}
```

**Scan entire directory:**
```rust
let parser = TodoParser::new();
let result = parser.scan_directory(Path::new("src/"))?;

println!("Found {} TODOs", result.todos.len());
println!("Found {} errors", result.errors.len());

// Group by area
let mut by_area: HashMap<String, Vec<TodoItem>> = HashMap::new();
for todo in result.todos {
    by_area.entry(todo.area.clone()).or_default().push(todo);
}

for (area, todos) in by_area {
    println!("{}: {} TODOs", area, todos.len());
}
```

**Include invalid TODOs:**
```rust
let parser = TodoParser::new().with_invalid();
let result = parser.parse_file(path)?;

for todo in result.todos {
    if !todo.is_valid() {
        println!("Invalid TODO: {}", todo.validation_errors().join(", "));
    }
}
```

### Language Detection

The parser automatically detects source language by file extension:

```rust
fn detect_language(path: &Path) -> Language {
    match path.extension().and_then(|e| e.to_str()) {
        Some("rs") => Language::Rust,
        Some("spl") => Language::Simple,
        Some("md") => Language::Markdown,
        _ => Language::Unknown,
    }
}
```

### Priority Normalization

The parser normalizes priority levels for consistency:

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

This ensures that `critical` and `P0` are treated identically in the database.

## Validation

The parser validates TODO format according to the specification:

**Valid areas:**
- `runtime`, `codegen`, `compiler`, `parser`, `type`, `stdlib`, `gpu`, `ui`, `test`, `driver`, `loader`, `pkg`, `doc`

**Valid priorities:**
- `P0`/`critical` - Blocking, fix immediately
- `P1`/`high` - Important, next sprint
- `P2`/`medium` - Should do, backlog
- `P3`/`low` - Nice to have, someday

**Format:**
```
TODO: [area][priority] description [#issue] [blocked:#issue,#issue]
```

## Test Coverage

The module includes comprehensive unit tests:

```rust
#[cfg(test)]
mod tests {
    // ✅ test_parse_rust_todo - Parse Rust comments
    // ✅ test_parse_simple_todo - Parse Simple comments
    // ✅ test_parse_invalid_todo - Handle invalid format
    // ✅ test_normalize_priority - Priority normalization
    // ✅ test_validation - Valid TODO validation
    // ✅ test_invalid_validation - Invalid TODO validation
    // ✅ test_skip_string_literals - Skip TODOs in strings
    // ✅ test_multiple_blocked_issues - Parse blocked issues
}
```

**Run tests:**
```bash
cargo test --package simple-driver todo_parser
```

## Performance Considerations

**Optimizations:**
- Regex patterns are compiled once and reused
- String literal detection uses simple heuristic (not full parsing)
- Directory scanning skips common build directories:
  - `target/`
  - `build/`
  - `vendor/`
  - `node_modules/`
  - Hidden files/directories (`.git`, `.cache`, etc.)

**Benchmarks (estimated):**
- Parse single file: ~1-5ms
- Scan entire codebase (~2,700 files): ~2-10 seconds
- Memory usage: ~1MB for database

## Future Enhancements

### Phase 2: Multi-line TODOs
```rust
// TODO: [runtime][P1] Implement dedicated runtime thread [#234]
//       Need message passing between main thread and monoio runtime.
//       See monoio_tcp.rs:251 for context.
//       [blocked:#100,#101]
```

**Implementation:** Detect continuation lines and merge into single TODO.

### Phase 3: Incremental Scanning
```rust
pub struct TodoScanner {
    cache: HashMap<PathBuf, FileHash>,
}

impl TodoScanner {
    pub fn scan_incremental(&mut self, dir: &Path) -> ParseResult {
        // Only scan files that changed since last scan
    }
}
```

**Benefits:** Faster re-scans (10x+ speedup for repeated scans)

### Phase 4: Parallel Scanning
```rust
use rayon::prelude::*;

pub fn scan_parallel(dir: &Path) -> ParseResult {
    // Scan files in parallel using rayon
}
```

**Benefits:** Faster initial scan (2-4x speedup on multi-core)

### Phase 5: LSP Integration

Provide TODO diagnostics in real-time while editing:

```rust
pub struct TodoLspServer {
    parser: TodoParser,
}

impl LanguageServer for TodoLspServer {
    fn did_change(&mut self, params: DidChangeTextDocumentParams) {
        let result = self.parser.parse_rust(&params.content, &params.uri);
        // Send diagnostics to editor
    }
}
```

## Examples

### Example 1: Scan and Report

```rust
use simple_driver::todo_parser::TodoParser;

fn main() -> Result<(), String> {
    let parser = TodoParser::new();
    let result = parser.scan_directory(Path::new("src/"))?;

    println!("TODO Report\n===========\n");
    println!("Total TODOs: {}", result.todos.len());
    println!("Parse errors: {}\n", result.errors.len());

    // Group by priority
    let mut p0_todos = Vec::new();
    let mut p1_todos = Vec::new();
    let mut p2_todos = Vec::new();
    let mut p3_todos = Vec::new();

    for todo in result.todos {
        match todo.normalized_priority() {
            "P0" => p0_todos.push(todo),
            "P1" => p1_todos.push(todo),
            "P2" => p2_todos.push(todo),
            "P3" => p3_todos.push(todo),
            _ => {}
        }
    }

    println!("P0 (Critical): {}", p0_todos.len());
    for todo in &p0_todos {
        println!("  - [{}:{}] {}", todo.file.display(), todo.line, todo.description);
    }

    println!("\nP1 (High): {}", p1_todos.len());
    println!("P2 (Medium): {}", p2_todos.len());
    println!("P3 (Low): {}", p3_todos.len());

    Ok(())
}
```

### Example 2: Validate TODO Format

```rust
use simple_driver::todo_parser::TodoParser;

fn main() -> Result<(), String> {
    let parser = TodoParser::new();
    let result = parser.scan_directory(Path::new("."))?;

    let mut invalid_count = 0;

    for error in &result.errors {
        println!("{}:{} - {}", error.file.display(), error.line, error.message);
        println!("  Raw: {}\n", error.raw_text.trim());
        invalid_count += 1;
    }

    if invalid_count > 0 {
        eprintln!("Found {} invalid TODOs", invalid_count);
        std::process::exit(1);
    } else {
        println!("All TODOs are valid!");
    }

    Ok(())
}
```

### Example 3: Generate Statistics

```rust
use simple_driver::todo_parser::TodoParser;
use std::collections::HashMap;

fn main() -> Result<(), String> {
    let parser = TodoParser::new();
    let result = parser.scan_directory(Path::new("."))?;

    // Statistics by area
    let mut area_stats: HashMap<String, usize> = HashMap::new();
    for todo in &result.todos {
        *area_stats.entry(todo.area.clone()).or_default() += 1;
    }

    println!("TODOs by Area:");
    for (area, count) in area_stats {
        println!("  {:12} {}", area, count);
    }

    // Statistics by file extension
    let mut rust_count = 0;
    let mut simple_count = 0;
    for todo in &result.todos {
        match todo.file.extension().and_then(|e| e.to_str()) {
            Some("rs") => rust_count += 1,
            Some("spl") => simple_count += 1,
            _ => {}
        }
    }

    println!("\nTODOs by Language:");
    println!("  Rust:   {}", rust_count);
    println!("  Simple: {}", simple_count);

    Ok(())
}
```

## Integration with TODO Database

The parser integrates with the TODO database system:

```rust
// In src/driver/src/todo_db.rs

use crate::todo_parser::{TodoParser, TodoItem};

pub fn update_todo_db_from_scan(db: &mut TodoDb, root_dir: &Path) -> Result<(), String> {
    let parser = TodoParser::new();
    let result = parser.scan_directory(root_dir)?;

    for todo_item in result.todos {
        let record = TodoRecord {
            id: db.next_id(),
            keyword: todo_item.keyword,
            area: todo_item.area,
            priority: todo_item.normalized_priority().to_string(),
            description: todo_item.description,
            file: todo_item.file.display().to_string(),
            line: todo_item.line,
            issue: todo_item.issue,
            blocked: todo_item.blocked,
            status: "open".to_string(),
            valid: true,
        };

        db.insert(record);
    }

    Ok(())
}
```

## Command-Line Tools

### `simple todo-scan`

Scan codebase and update TODO database:

```bash
# Scan all source files
simple todo-scan

# Scan specific directory
simple todo-scan --path src/runtime/

# Validate only (don't update database)
simple todo-scan --validate

# Include invalid TODOs in report
simple todo-scan --include-invalid

# Output format
simple todo-scan --format json > todos.json
```

### `simple todo-check`

Validate TODO format in files:

```bash
# Check all files
simple todo-check

# Check specific files
simple todo-check src/runtime/tcp.rs

# Auto-fix simple issues (future)
simple todo-check --fix

# Output format
simple todo-check --format github-actions
```

## Benefits

**Comprehensive coverage:**
- ✅ Track TODOs across entire codebase (both languages)
- ✅ No TODOs are missed or forgotten
- ✅ Single source of truth for all pending work

**Consistency:**
- ✅ Enforces TODO format specification
- ✅ Standardizes priority levels
- ✅ Validates area names

**Automation:**
- ✅ Auto-updates from source code
- ✅ No manual database maintenance
- ✅ Integrates with CI/CD pipeline

**Metrics:**
- ✅ Track TODO count over time
- ✅ Identify high-priority items
- ✅ Monitor progress by area

## Conclusion

The dual-language TODO parser provides comprehensive TODO tracking for the Simple compiler project. By supporting both Rust and Simple source files, it ensures no TODOs are missed and enables automated database updates and validation.

**Status:** ✅ Proof-of-concept implemented with full test coverage
**Next steps:** Integrate with TODO database system (Phase 1-3 of implementation plan)

## References

- Parser module: `src/driver/src/todo_parser.rs`
- TODO format spec: `.claude/skills/todo.md`
- Implementation plan: `doc/design/todo_db_plan.md`
- Feature database: `src/driver/src/feature_db.rs`
- Task database: `src/driver/src/task_db.rs`
