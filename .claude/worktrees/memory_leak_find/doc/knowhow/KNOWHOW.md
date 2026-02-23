# Development Know-How

This document contains practical development tips, workflows, and gotchas for the Simple language compiler project.

## Version Control: Why Jujutsu (jj) Instead of Git?

This project uses **Jujutsu (jj)** for version control, not git directly.

### Key Differences

| Aspect | Git | Jujutsu (jj) |
|--------|-----|--------------|
| Working copy | Separate from commits | Is a commit |
| Staging area | Required (`git add`) | Automatic (all changes tracked) |
| Branches | Required | Optional (use bookmarks) |
| Commit amend | Rewrites history (`--amend`) | Natural operation |
| Merge conflicts | Blocking | Non-blocking (can defer resolution) |
| Undo | Complex (`git reflog`) | Simple (`jj undo`) |

### Common Workflows

**Daily development:**

```bash
# Check status
jj status

# Create a commit
jj commit -m "Add feature X"

# Amend the current commit
jj commit --amend -m "Updated message"

# View history
jj log

# Undo last operation
jj undo
```

**Pushing changes:**

```bash
# Set bookmark and push (always work on main)
jj bookmark set main -r @
jj git push --bookmark main

# One-liner
jj bookmark set main -r @ && jj git push --bookmark main
```

**Syncing with remote:**

```bash
# Fetch changes
jj git fetch

# Rebase onto remote main
jj rebase -d main@origin
```

### Git Hook Protection

This repository has a **pre-commit hook** that warns when direct git commands are used:

- **Location:** `.git/hooks/pre-commit`
- **Behavior:** Warns but doesn't block (safe for jj operations)
- **Detection:** Checks for `JJ_OP_ID` environment variable

The hook will show a warning if you accidentally use `git commit`, but allows the commit to proceed. This prevents breaking jj's internal operations while reminding developers to use jj.

**Testing the hook:**

```bash
# This will trigger the warning (but still commit)
git commit -m "test"

# This will proceed silently (jj's internal git usage)
jj commit -m "test"
```

### Why Not Use Git Directly?

1. **Automatic tracking**: No need for `git add` - all changes are tracked
2. **Safe experiments**: Every operation is reversible with `jj undo`
3. **Better conflict handling**: Conflicts don't block operations
4. **Simpler mental model**: Working copy is just another commit
5. **Powerful rewriting**: Amending and rebasing are first-class operations

See the `/versioning` skill (`.claude/skills/versioning.md`) for complete jj documentation.

---

## Build System

### Quick Commands

```bash
# Format, lint, and test (run before commits)
make check

# Full validation (includes coverage and duplication check)
make check-full

# Run all tests (Rust + Simple/SSpec)
make test-all

# Build Rust runtime
cd rust && cargo build                    # Debug
cd rust && cargo build --release          # Release (optimized)
```

### Binary Architecture

| Binary | Location | Purpose |
|--------|----------|---------|
| `simple_runtime` | `rust/target/debug/simple_runtime` | Core runtime (Rust) |
| `simple` | `bin/wrappers/simple` | CLI wrapper (Shell → Simple) |
| `simple_stub` | `bin/wrappers/simple_stub` | Stub wrapper |

All user-facing tools are Simple apps in `src/app/`, executed by the Rust runtime.

### Recompile After Changes

```bash
# Rebuild Rust runtime (after Rust changes)
cd rust && cargo build

# Check for warnings/errors (limit output)
cd rust && cargo build 2>&1 | head -20

# Run Simple script directly
./rust/target/debug/simple_runtime script.spl

# Run via CLI wrapper
./bin/wrappers/simple script.spl
```

---

## Testing

### Test Types

| Type | Marker | Auto-Ignored? | Run With |
|------|--------|---------------|----------|
| Regular | `it "..."` | No | `simple test` |
| Slow | `slow_it "..."` | Yes | `simple test --only-slow` |
| Skipped | Tag: `skip` | No | `simple test --only-skipped` |
| Doc-tests | ` ```rust` | Some | `cargo test --doc` |

### Common Test Commands

```bash
# Quick feedback (excludes slow tests)
./rust/target/debug/simple_runtime test

# Run slow tests separately
./rust/target/debug/simple_runtime test --only-slow

# Run specific test file
./rust/target/debug/simple_runtime test path/to/spec.spl

# List tests without running
./rust/target/debug/simple_runtime test --list

# Run Rust tests
cd rust && cargo test --workspace

# Run doc-tests
cd rust && cargo test --doc --workspace

# Full test suite (before committing)
make test-all
```

### Auto-Generated Documentation

These files update automatically during development:

| File | Updated When | Command |
|------|-------------|---------|
| `doc/feature/pending_feature.md` | Every test run | `simple test` |
| `doc/test/test_result.md` | Every test run | `simple test` |
| `doc/build/recent_build.md` | Every build | `simple build` |
| `doc/TODO.md` | Manual | `simple todo-scan` |

**Quick checks:**
- What needs work? → `doc/feature/pending_feature.md`
- Test results? → `doc/test/test_result.md`
- Build status? → `doc/build/recent_build.md`

---

## Code Style

### Variables

```simple
val name = "Alice"    # Immutable (preferred)
var count = 0         # Mutable
```

### Generics: Use `<>` NOT `[]`

✅ **Correct:**
```simple
Option<T>
List<Int>
fn map<T, U>(f: fn(T) -> U) -> U
```

❌ **Wrong (deprecated):**
```simple
Option[T]      # Shows compiler warning
List[Int]      # Will be removed in v1.0.0
```

### Constructors: Direct Construction

✅ **Preferred:**
```simple
val p = Point(x: 3, y: 4)                                           # Direct
val interner = StringInterner(strings: {}, reverse: {}, next_id: 0) # Direct
```

✅ **Optional (for special cases):**
```simple
val center = Point.origin()                       # Named factory
val interner = StringInterner.with_capacity(100)  # Named factory
```

❌ **Wrong:**
```simple
val p = Point.new(3, 4)        # Don't use .new() - not idiomatic
```

### Methods

```simple
class Point:
    x: i64
    y: i64

    fn distance() -> f64:              # Immutable (self implicit)
        (self.x * self.x + self.y * self.y).sqrt()

    me move(dx: i64, dy: i64):         # Mutable ('me' keyword)
        self.x = self.x + dx
        self.y = self.y + dy

    static fn origin() -> Point:       # Static factory
        Point(x: 0, y: 0)
```

### Existence Checks: Use `.?` NOT `is_*`

✅ **Preferred:**
```simple
opt.?                         # Instead of opt.is_some()
not opt.?                     # Instead of opt.is_none()
list.first.?                  # Instead of list.first().is_some()
result.ok.?                   # Instead of result.is_ok()
```

### Config Files: Use SDN NOT JSON/YAML

✅ **Correct:**
```sdn
# simple.sdn
package:
  name: my-project
  version: 1.0.0

dependencies:
  http: 2.0
```

❌ **Wrong:**
```json
// Don't use JSON for Simple configs
{"package": {"name": "my-project"}}
```

---

## Common Gotchas

### 1. Question Mark `?` is NOT for Method Names

❌ **Wrong (Ruby-style):**
```simple
fn is_empty?():              # ERROR: ? not allowed in names
    self.len() == 0
```

✅ **Correct:**
```simple
fn is_empty():               # Use plain name
    self.len() == 0

# Or use .? operator for existence checks
list.?                       # true if non-empty
```

### 2. Caret `^` Only in Math Blocks

❌ **Wrong:**
```simple
val result = x^2             # ERROR: ^ not allowed outside m{}
```

✅ **Correct:**
```simple
val result = x ** 2          # Use ** for power
val formula = m{ x^2 }       # Or use m{} math block
```

### 3. Don't Remove TODO Markers

❌ **Wrong:**
```simple
# Implementation done!       # TODO removed but feature incomplete
fn feature():
    ()                        # Still returns unit!
```

✅ **Correct:**
```simple
# TODO(P1): Complete implementation
fn feature():
    ()                        # TODO marker stays until fully working
```

### 4. Git vs Jujutsu

❌ **Wrong:**
```bash
git commit -m "fix bug"
git push
```

✅ **Correct:**
```bash
jj commit -m "fix bug"
jj bookmark set main -r @
jj git push --bookmark main
```

---

## Debugging

### Runtime Debugging

```bash
# Run with debug output
RUST_LOG=debug ./rust/target/debug/simple_runtime script.spl

# GC logging
RUST_LOG=simple_gc=trace ./rust/target/debug/simple_runtime script.spl

# Interpreter tracing
SIMPLE_TRACE=1 ./rust/target/debug/simple_runtime script.spl
```

### Lint Debugging

```bash
# Dry-run (preview fixes)
./bin/wrappers/simple fix file.spl --dry-run

# Apply all fixes
./bin/wrappers/simple fix file.spl --fix-all

# Interactive mode
./bin/wrappers/simple fix file.spl --fix-interactive
```

See the `/debug` skill for complete debugging guide.

---

## Documentation Writing

### SSpec Tests (Executable Specs)

Use the template for new specs:

```bash
# Copy template
cp .claude/templates/sspec_template.spl test/path/to/new_spec.spl

# See complete example
cat doc/guide/sspec_complete_example.md

# Or use skill
# /sspec
```

**Key features:**
- Tests generate documentation automatically
- Use `feature`, `scenario`, `it`, `pending` markers
- Add `tags: [tag1, tag2]` for filtering

### Documentation Types

| Type | Location | Purpose |
|------|----------|---------|
| Research | `doc/research/` | Investigation, exploration |
| Design | `doc/design/` | Architecture decisions |
| Guides | `doc/guide/` | User tutorials |
| Specs | `test/**/*_spec.spl` | Executable SSpec tests |

See the `/doc` skill for complete documentation guide.

---

## Performance Tips

### 1. Prefer Release Builds for Benchmarks

```bash
cd rust && cargo build --release
./rust/target/release/simple_runtime benchmark.spl
```

### 2. Use `--only-slow` Separately

```bash
# Quick feedback loop
./rust/target/debug/simple_runtime test

# Run slow tests separately (before commit)
./rust/target/debug/simple_runtime test --only-slow
```

### 3. Parallel Test Execution

Tests run in parallel by default. Use `--test-threads=1` for debugging:

```bash
./rust/target/debug/simple_runtime test --test-threads=1
```

---

## Skills Quick Reference

Invoke with `/<skill-name>` for detailed guidance:

| Skill | Purpose |
|-------|---------|
| `versioning` | Jujutsu (jj) workflow |
| `test` | Test writing (Rust & SSpec) |
| `sspec` | SSpec BDD framework |
| `coding` | Coding standards |
| `design` | Design patterns, APIs |
| `architecture` | Compiler architecture |
| `debug` | Debugging, tracing, GC |
| `doc` | Documentation writing |
| `stdlib` | Writing stdlib modules |
| `todo` | TODO/FIXME format |

Skills located in `.claude/skills/`.

---

## Getting Help

- **Syntax reference:** `doc/guide/syntax_quick_reference.md`
- **SSpec template:** `.claude/templates/sspec_template.spl`
- **Project instructions:** `CLAUDE.md`
- **Bug reports:** `doc/bug_report.md`
- **Feature requests:** `doc/improve_request.md`
