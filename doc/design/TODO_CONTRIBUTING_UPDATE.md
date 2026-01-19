# TODO System - CONTRIBUTING.md Update (Ready to Add)

**Status:** Ready to copy-paste into CONTRIBUTING.md
**When:** After binary builds successfully

## Section to Add to CONTRIBUTING.md

Add this section to your `CONTRIBUTING.md` file, suggested location: after "Code Style" and before "Testing".

---

## TODO Comment Format

All TODO and FIXME comments in the codebase must follow a standardized format to enable automated tracking and management.

### Format Specification

```
TODO: [area][priority] description [#issue] [blocked:#issue,#issue]
FIXME: [area][priority] description [#issue] [blocked:#issue,#issue]
```

**Required components:**
- **Keyword:** `TODO:` or `FIXME:`
- **Area:** Component or subsystem (see list below)
- **Priority:** Urgency level (see list below)
- **Description:** What needs to be done

**Optional components:**
- **Issue number:** GitHub issue ID (e.g., `[#123]`)
- **Blocked by:** Dependencies (e.g., `[blocked:#100,#101]`)

### Valid Areas

Choose the most appropriate area for your TODO:

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

### Valid Priorities

Choose one of these priority levels:

| Priority | Alias | Meaning |
|----------|-------|---------|
| `P0` | `critical` | Blocking issue, fix immediately |
| `P1` | `high` | Important, should be in next sprint |
| `P2` | `medium` | Should do, add to backlog |
| `P3` | `low` | Nice to have, someday/maybe |

**Guidelines:**
- Use `P0`/`critical` for: crashes, security issues, blockers
- Use `P1`/`high` for: important features, significant bugs
- Use `P2`/`medium` for: nice-to-have features, minor bugs
- Use `P3`/`low` for: future work, optimizations, tech debt

### Examples

**Rust code:**

```rust
// TODO: [runtime][P0] Implement monoio TCP write [#234]
// TODO: [stdlib][critical] Fix memory leak [#567] [blocked:#123]
// FIXME: [parser][P2] Handle edge case in expression parsing
// TODO: [gpu][P1] Create Vector3 variant [#789] [blocked:#100,#101]
// TODO: [compiler][P3] Optimize type inference performance
```

**Simple code:**

```simple
# TODO: [stdlib][P0] Implement socket write via FFI [#234]
# TODO: [gpu][critical] Fix render pipeline memory leak [#567]
# FIXME: [ui][P2] Improve button click handling
# TODO: [doc][P1] Add examples section [#789] [blocked:#100]
# TODO: [test][P3] Add property-based tests
```

**Markdown documentation:**

```markdown
<!-- TODO: [doc][P1] Add architecture diagram [#123] -->
<!-- FIXME: [doc][P2] Update outdated API examples -->
```

### Why This Format?

This standardized format enables:

1. **Automated tracking:** TODOs are automatically extracted and tracked in a database
2. **Prioritization:** Easy identification of critical vs. low-priority items
3. **Organization:** TODOs grouped by component area
4. **Dependencies:** Track blocking relationships between TODOs
5. **Metrics:** Generate statistics on technical debt

### Validation

Before committing code with TODOs, validate the format:

```bash
# Check TODO format
make check-todos

# Or manually
./target/debug/simple todo-scan --validate
```

The CI pipeline will reject commits with invalid TODO format.

### Viewing TODOs

To see all TODOs in the project:

```bash
# Generate TODO documentation
make gen-todos

# View the documentation
cat doc/TODO.md

# Show critical TODOs
make todos-p0

# Show statistics
make todos-stats
```

### TODO Workflow

1. **Write code** with properly formatted TODOs
2. **Validate format** with `make check-todos`
3. **Link to issue** (optional but recommended)
4. **Mark dependencies** if blocked by other work
5. **Commit** - CI will validate format
6. **Update database** periodically with `make gen-todos`

### Common Mistakes

❌ **Invalid - Missing area and priority:**
```rust
// TODO: implement this feature
```

✅ **Valid:**
```rust
// TODO: [compiler][P2] implement this feature
```

---

❌ **Invalid - Wrong area name:**
```rust
// TODO: [backend][P1] add caching
```

✅ **Valid:**
```rust
// TODO: [runtime][P1] add caching
```

---

❌ **Invalid - Wrong priority format:**
```rust
// TODO: [stdlib][high priority] fix bug
```

✅ **Valid:**
```rust
// TODO: [stdlib][P1] fix bug
// or
// TODO: [stdlib][high] fix bug
```

### For More Information

- **Complete specification:** `.claude/skills/todo.md`
- **Technical documentation:** `doc/design/dual_language_todo_parsing.md`
- **Quick start guide:** `doc/design/TODO_QUICKSTART.md`

---

## Alternative: Shorter Version

If you prefer a shorter version for CONTRIBUTING.md, use this:

---

## TODO Comments

All TODO/FIXME comments must follow this format:

```
TODO: [area][priority] description [#issue] [blocked:#issue]
```

**Example:**
```rust
// TODO: [runtime][P0] Implement monoio TCP write [#234]
```

**Valid areas:** runtime, codegen, compiler, parser, type, stdlib, gpu, ui, test, driver, loader, pkg, doc

**Valid priorities:** P0/critical, P1/high, P2/medium, P3/low

**Validate before commit:**
```bash
make check-todos
```

See `.claude/skills/todo.md` for complete specification.

---

## Installation Instructions

### Step 1: Choose Version

Choose either:
- **Full version** - Complete explanation (recommended)
- **Short version** - Brief reference

### Step 2: Find Insert Location

Open `CONTRIBUTING.md` and find a good location, suggested:
- After "Code Style" section
- Before "Testing" section
- Or create new "Development Guidelines" section

### Step 3: Add Content

Paste the chosen version into `CONTRIBUTING.md`.

### Step 4: Update Table of Contents

If CONTRIBUTING.md has a table of contents, add:

```markdown
- [TODO Comment Format](#todo-comment-format)
  - [Format Specification](#format-specification)
  - [Valid Areas](#valid-areas)
  - [Valid Priorities](#valid-priorities)
  - [Examples](#examples)
  - [Validation](#validation)
```

### Step 5: Test Links

Verify all internal links work:
- `.claude/skills/todo.md`
- `doc/design/dual_language_todo_parsing.md`
- `doc/design/TODO_QUICKSTART.md`

### Step 6: Commit

```bash
git add CONTRIBUTING.md
jj bookmark set main -r @
jj git push --bookmark main
```

## Checklist

- [ ] Choose version (full or short)
- [ ] Find insert location in CONTRIBUTING.md
- [ ] Paste content
- [ ] Update table of contents (if exists)
- [ ] Verify links work
- [ ] Test examples
- [ ] Commit changes

## After Installation

Contributors should now:
1. Read the TODO format specification
2. Use the format in all new TODOs
3. Run `make check-todos` before committing
4. View `doc/TODO.md` to see project TODOs

## Additional Suggestions

### Add to PR Template

If you have a PR template, add:

```markdown
## Checklist

- [ ] Code follows project style guide
- [ ] Tests added/updated
- [ ] Documentation updated
- [ ] TODOs properly formatted (`make check-todos` passes)
```

### Add to New Contributor Guide

In onboarding documentation:

```markdown
### Adding TODOs

When adding TODOs to code, use this format:

```rust
// TODO: [area][priority] description [#issue]
```

Run `make check-todos` to validate before committing.
See CONTRIBUTING.md for details.
```

### Add to Code Review Guidelines

In review checklist:

- [ ] TODOs are properly formatted
- [ ] Critical TODOs (P0) have issue numbers
- [ ] Blocked TODOs reference blocking issues
