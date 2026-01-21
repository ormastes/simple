<!-- skip_todo -->

# Markdown TODO Skip Design

**Date:** 2026-01-21
**Status:** Design Proposal

## Problem

Documentation files that explain the TODO system contain example TODO comments that get picked up by `simple todo-scan` as real TODOs. This creates noise in the TODO database.

Currently, skip_todo works for:
- Rust files: `#![skip_todo]` in module doc comments
- Simple files: `# #![skip_todo]` in file header

But markdown files (`.md`) have no way to skip TODO scanning.

## Solution

Add skip_todo support for markdown files using HTML comments.

### Syntax Options

**Option 1: HTML Comment (Recommended)**
```markdown
<!-- skip_todo -->

# Document Title

This file contains example TODOs:
<!-- TODO: [doc][P1] Add examples [#234] -->
```

**Option 2: Frontmatter-style**
```markdown
---
skip_todo: true
---

# Document Title
```

**Option 3: Attribute-style**
```markdown
<!-- #![skip_todo] -->

# Document Title
```

## Recommended: Option 1

**Rationale:**
- Simple and clear
- Consistent with markdown comment syntax
- Easy to implement
- No YAML parsing needed
- Matches the spirit of Rust/Simple `#![skip_todo]`

### Implementation

**Detection Pattern:**
```rust
// In todo_parser.rs, check first 10 lines for:
r"<!--\s*skip_todo\s*-->"
r"<!--\s*#!\[skip_todo\]\s*-->"
r"<!--\s*#!\[allow\(todo_format\)\]\s*-->"
```

**Placement:**
- Must appear in first 10 lines of file
- Typically at the very top (line 1-3)
- Can be combined with title

### Examples

**Minimal:**
```markdown
<!-- skip_todo -->
# TODO System Documentation
```

**With explanation:**
```markdown
<!-- skip_todo - This file contains example TODOs for documentation -->

# TODO Format Specification

Example TODOs:
<!-- TODO: [doc][P1] Add examples [#234] -->
```

**Multiple syntaxes (all supported):**
```markdown
<!-- skip_todo -->
<!-- #![skip_todo] -->
<!-- #![allow(todo_format)] -->
```

## Files That Should Use skip_todo

**Design documentation about TODO system:**
- `doc/design/IMPLEMENTATION_SUMMARY.md`
- `doc/design/TODO_CONTRIBUTING_UPDATE.md`
- `doc/design/TODO_QUICKSTART.md`
- `doc/design/TODO_SYSTEM_COMPLETE.md`
- `doc/design/dual_language_parsing_summary.md`
- `doc/design/dual_language_todo_parsing.md`

**Skills with TODO examples:**
- `.claude/skills/todo.md`

## Comparison with Other Languages

| Language | Syntax | Location |
|----------|--------|----------|
| Rust | `//! #![skip_todo]` | Module doc comment |
| Simple | `# #![skip_todo]` | File header |
| Markdown | `<!-- skip_todo -->` | First 10 lines |

## Implementation Checklist

- [ ] Update `src/rust/driver/src/todo_parser.rs` to detect markdown skip_todo
- [ ] Add tests for markdown skip_todo detection
- [ ] Update `.claude/skills/todo.md` documentation
- [ ] Add skip_todo to design docs that contain examples
- [ ] Test with `simple todo-scan`

## Future Enhancements

- Support skip_todo for specific sections (not just whole file)
- Add `<!-- skip_todo:start -->` and `<!-- skip_todo:end -->` markers
- Lint rule to suggest skip_todo for files with many example TODOs
