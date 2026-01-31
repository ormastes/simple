<!-- skip_todo -->

# TODO Skill - Comment Format Specification

## Format

```
TODO: [area][priority] description [#issue] [blocked:#issue,#issue]
FIXME: [area][priority] description [#issue] [blocked:#issue,#issue]
```

### Components

| Component | Required | Format | Examples |
|-----------|----------|--------|----------|
| Keyword | Yes | `TODO:` or `FIXME:` | `TODO:`, `FIXME:` |
| Area | Yes | `[area]` | `[runtime]`, `[stdlib]`, `[codegen]` |
| Priority | Yes | `[P0-P3]` or `[name]` | `[P0]`, `[critical]`, `[high]` |
| Description | Yes | Free text | `Implement socket write` |
| Issue | No | `[#number]` | `[#234]` |
| Blocked | No | `[blocked:#n,#m]` | `[blocked:#123,#456]` |

### Priority Levels

| Level | Aliases | Meaning |
|-------|---------|---------|
| P0 | `critical` | Blocking, fix immediately |
| P1 | `high` | Important, next sprint |
| P2 | `medium` | Should do, backlog |
| P3 | `low` | Nice to have, someday |

### Areas

| Area | Scope |
|------|-------|
| `runtime` | GC, values, monoio, concurrency |
| `codegen` | MIR, Cranelift, LLVM, Vulkan |
| `compiler` | HIR, pipeline, interpreter |
| `parser` | Lexer, AST, parsing |
| `type` | Type checker, inference |
| `stdlib` | Simple standard library |
| `gpu` | GPU/SIMD/graphics |
| `ui` | UI framework |
| `test` | Test frameworks |
| `driver` | CLI, tools |
| `loader` | SMF loader |
| `pkg` | Package manager |
| `doc` | Documentation, specs, guides |

## Examples

### Markdown

```markdown
<!-- TODO: [doc][P1] Add examples section [#234] -->

> **TODO** [stdlib][P2]: Document variant selection API

- [ ] **TODO** [test][P1]: Add integration test cases [#789]
- [ ] **FIXME** [doc][critical]: Update outdated diagram [#890]

| Status | Task |
|--------|------|
| TODO [compiler][P2] | Document MIR instructions |
| FIXME [runtime][P1] | Fix GC section [#456] |
```

**Formats:**
1. HTML comment: `<!-- TODO: [area][priority] description -->`
2. Blockquote: `> **TODO** [area][priority]: description`
3. Checkbox: `- [ ] **TODO** [area][priority]: description [#issue]`
4. Table cell: `TODO [area][priority]` in content

### Rust

```rust
// TODO: [runtime][P0] Implement monoio TCP write [#234]
// TODO: [runtime][critical] Fix memory barrier race [#567] [blocked:#123]
// TODO: [codegen][P1] Track line numbers in HIR [#789]
// TODO: [codegen][high] Add SPIR-V validation
// TODO: [compiler][P2] Implement SDN parsing [blocked:#100,#101]
// TODO: [parser][P3] Parse !Trait syntax [#1151]
// FIXME: [runtime][P0] Memory leak in GC barrier [#890]
// FIXME: [type][critical] Incorrect unification [#891] [blocked:#500]
```

### Simple

```simple
# TODO: [stdlib][P0] Implement via FFI [#234]
# TODO: [stdlib][critical] Fix memory corruption [#567]
# TODO: [gpu][P1] Create Vector3 variant [#789] [blocked:#100]
# TODO: [gpu][high] Implement render commands
# TODO: [stdlib][P2] Add JSON parsing [blocked:#200,#201]
# TODO: [test][P3] Add edge case tests
# FIXME: [stdlib][P0] Incorrect return value [#890]
# FIXME: [ui][critical] Layout crash [#891] [blocked:#400,#401]
```

### Multi-line (complex description)

```rust
// TODO: [runtime][P1] Implement dedicated runtime thread [#234]
//       Need message passing between main thread and monoio runtime.
//       See monoio_tcp.rs:251 for context.
//       [blocked:#100,#101]
```

```simple
# TODO: [stdlib][P1] Implement file watching [#345]
#       Need to use platform-specific APIs:
#       - Linux: inotify
#       - macOS: FSEvents
#       - Windows: ReadDirectoryChangesW
#       [blocked:#200]
```

## Quick Reference

```
TODO: [area][P0|P1|P2|P3] description [#issue] [blocked:#n,#m]
      │      │            │            │        └── Optional: blocking issues
      │      │            │            └── Optional: related issue
      │      │            └── Required: what needs to be done
      │      └── Required: P0/critical, P1/high, P2/medium, P3/low
      └── Required: runtime, codegen, compiler, parser, stdlib, gpu, etc.
```

## Regex Patterns

### Code Comments (Rust/Simple)
```regex
(TODO|FIXME):\s*\[(\w+)\]\[(\w+)\]\s*(.+?)(?:\s*\[#(\d+)\])?(?:\s*\[blocked:(#\d+(?:,#\d+)*)\])?$
```

### Markdown HTML Comment
```regex
<!--\s*(TODO|FIXME):\s*\[(\w+)\]\[(\w+)\]\s*(.+?)(?:\s*\[#(\d+)\])?(?:\s*\[blocked:[^\]]+\])?\s*-->
```

### Markdown Blockquote
```regex
>\s*\*\*(TODO|FIXME)\*\*\s*\[(\w+)\]\[(\w+)\]:\s*(.+?)(?:\s*\[#(\d+)\])?$
```

### Markdown Checkbox
```regex
-\s*\[\s*\]\s*\*\*(TODO|FIXME)\*\*\s*\[(\w+)\]\[(\w+)\]:\s*(.+?)(?:\s*\[#(\d+)\])?$
```

### Capture Groups
1. Keyword (TODO/FIXME)
2. Area
3. Priority
4. Description
5. Issue number (optional)
6. Blocked issues (optional)

## Lint Rules

Enforced by `simple/app/lint/main.spl`:

| Code | Level | Description |
|------|-------|-------------|
| T001 | Warn | TODO/FIXME missing [area][priority] format |
| T002 | Warn | TODO/FIXME has invalid area |
| T003 | Warn | TODO/FIXME has invalid priority |
| T004 | Deny | P0/critical TODO must have issue number |

Run linter:
```bash
./rust/target/debug/simple simple/app/lint/main.spl <file.spl>
```

### Skipping TODO Checks

For files that discuss, parse, or process TODOs (like parsers, collectors, migration scripts, or documentation), you can skip TODO format checking using the `#![skip_todo]` attribute at the top of the file:

**Rust files:**
```rust
//! Module documentation
//!
//! #![skip_todo]

use std::...
```

**Simple files:**
```simple
# Module documentation
#
# #![skip_todo]

use core...
```

**Markdown files:**
```markdown
<!-- skip_todo -->

# Document Title

Documentation with example TODOs...
```

**Also supported (for flexibility):**
- Rust: `#![allow(todo_format)]` - Standard lint attribute syntax
- Rust/Simple: `// skip_todo` or `# skip_todo` - Comment-based skip
- Markdown: `<!-- #![skip_todo] -->` or `<!-- #![allow(todo_format)] -->` - HTML comment variants

**When to use:**
- TODO parser implementations
- TODO collector/scanner tools
- Migration scripts that process TODOs
- Documentation files with TODO format examples
- Test files that test TODO parsing

**Files already using skip_todo:**

Rust/Simple code:
- `rust/driver/src/todo_parser.rs`
- `rust/compiler/src/lint/checker.rs`
- `rust/compiler/src/lint/types.rs`
- `rust/compiler/src/lint/mod.rs`
- `src/lib/std/src/tooling/todo_parser.spl`
- `src/lib/std/src/tooling/dashboard/collectors/todo_collector.spl`
- `scripts/simple/migrate_todo.spl`

Markdown documentation:
- `.claude/skills/todo.md`
- `doc/design/IMPLEMENTATION_SUMMARY.md`
- `doc/design/TODO_CONTRIBUTING_UPDATE.md`
- `doc/design/TODO_QUICKSTART.md`
- `doc/design/TODO_SYSTEM_COMPLETE.md`
- `doc/design/dual_language_parsing_summary.md`
- `doc/design/dual_language_todo_parsing.md`

## TODO Documentation Generation

The TODO system automatically generates documentation when scanning:

**Command:** `simple todo-scan`

**Generated Files:**
1. `doc/todo/todo_db.sdn` - TODO database (SDN format)
2. `doc/TODO.md` - Human-readable TODO documentation (NEW: auto-generated)

**Workflow:**
```bash
# Scan codebase and generate docs (both files updated automatically)
simple todo-scan

# Output:
# Scanning TODOs from .
# Scan complete:
#   Added:   5 TODOs
#   Updated: 2 TODOs
#   Removed: 1 TODOs
#   Total:   71 TODOs
# Database saved to doc/todo/todo_db.sdn
# Generated docs to doc/TODO.md  ← Automatic!
```

**Legacy workflow (still works):**
```bash
# Old two-step process (still supported)
simple todo-scan   # Only update database
simple todo-gen    # Only generate docs
```

**doc/TODO.md Contents:**
- Statistics (total, open, blocked, stale)
- By Area table
- By Priority table
- P0 Critical TODOs section
- P1 High Priority TODOs section
- Blocked TODOs section
- Stale TODOs section

**Comparison with Feature System:**

| System | Command | Database | Docs | Updated |
|--------|---------|----------|------|---------|
| **TODO** | `simple todo-scan` | `doc/todo/todo_db.sdn` | `doc/TODO.md` | Manual command |
| **Feature** | `simple test` | `doc/feature/feature_db.sdn` | `doc/feature/*.md` | **Every test run** |

## Migration

**Script:** `scripts/simple/migrate_todo.spl`

```bash
# Dry run (preview changes)
./rust/target/debug/simple scripts/simple/migrate_todo.spl src/compiler/ --dry-run

# Migrate with verbose output
./rust/target/debug/simple scripts/simple/migrate_todo.spl src/runtime/ --verbose

# Migrate single file
./rust/target/debug/simple scripts/simple/migrate_todo.spl src/compiler/src/mock.rs
```

**Manual conversion:**
```
# Old
// TODO: Implement socket write

# New
// TODO: [runtime][P2] Implement socket write
```

## See Also

- `doc/TODO.md` - Project TODO list
- `doc/feature/` - Feature implementation status
- `.claude/skills/debug.md` - Debugging skill
