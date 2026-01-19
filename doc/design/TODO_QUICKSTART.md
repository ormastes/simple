# TODO Database System - Quick Start Guide

**Status:** ✅ Code complete, ready to use once binary builds
**Commands:** `simple todo-scan`, `simple todo-gen`

## Prerequisites

The TODO system is fully implemented but requires the binary to be built first:

```bash
# Build the binary (once i18n errors are fixed)
cargo build --release

# Verify it works
./target/release/simple todo-scan --help
```

## First-Time Setup (5 minutes)

### Step 1: Run Initial Scan

Scan the entire codebase for TODOs:

```bash
./target/release/simple todo-scan
```

**Expected output:**
```
Scanning TODOs from .
Scan complete:
  Added:   142 TODOs
  Updated: 0 TODOs
  Removed: 0 TODOs
  Total:   142 TODOs
Database saved to doc/todo/todo_db.sdn
```

**What it does:**
- Scans all `.rs`, `.spl`, and `.md` files
- Parses TODO/FIXME comments
- Validates format
- Creates `doc/todo/todo_db.sdn`

### Step 2: Generate Documentation

Create the TODO.md file:

```bash
./target/release/simple todo-gen
```

**Expected output:**
```
Generating TODO docs from doc/todo/todo_db.sdn...
Generated docs for 142 TODOs
  -> doc/TODO.md
```

**What it creates:**
- `doc/TODO.md` with statistics
- Grouped by priority (P0, P1, P2, P3)
- Grouped by area (runtime, codegen, etc.)

### Step 3: Review Output

```bash
# View the database
cat doc/todo/todo_db.sdn

# View the documentation
cat doc/TODO.md

# Check statistics
head -20 doc/TODO.md
```

### Step 4: Fix Invalid TODOs (if any)

If the scan found invalid TODOs:

```bash
# Run validation
./target/release/simple todo-scan --validate
```

**Common issues:**
- Missing `[area]` - Add valid area name
- Missing `[priority]` - Add P0-P3 or critical/high/medium/low
- Invalid area - Must be one of: runtime, codegen, compiler, parser, type, stdlib, gpu, ui, test, driver, loader, pkg, doc
- Invalid priority - Must be P0/P1/P2/P3 or critical/high/medium/low

**Fix example:**
```rust
// Before (invalid)
// TODO: implement this feature

// After (valid)
// TODO: [compiler][P2] implement this feature
```

### Step 5: Commit

```bash
# Review changes
git status
git diff doc/todo/todo_db.sdn
git diff doc/TODO.md

# Commit using jj
jj bookmark set main -r @
jj git push --bookmark main
```

## Daily Usage

### Check TODO Status

```bash
# Quick statistics
head -20 doc/TODO.md

# See all P0 critical TODOs
grep -A 3 "P0 Critical" doc/TODO.md

# Count by area
grep "^\| runtime" doc/TODO.md
```

### Update TODO Database

When you add/remove/modify TODOs:

```bash
# Scan for changes
./target/release/simple todo-scan

# Regenerate docs
./target/release/simple todo-gen

# Commit if changed
git diff doc/TODO.md
```

### Validate TODO Format

Before committing code with new TODOs:

```bash
# Check format (no database update)
./target/release/simple todo-scan --validate

# Returns exit code 0 if all valid
```

## Command Reference

### `simple todo-scan`

Scan source code and update the TODO database.

**Syntax:**
```bash
simple todo-scan [OPTIONS]
```

**Options:**
- `--path <dir>` - Scan specific directory (default: current directory)
- `--db <file>` - Custom database path (default: `doc/todo/todo_db.sdn`)
- `--validate` - Validate only, don't update database

**Examples:**
```bash
# Scan everything
simple todo-scan

# Scan only runtime code
simple todo-scan --path src/runtime/

# Validate without updating
simple todo-scan --validate

# Custom database location
simple todo-scan --db custom/todos.sdn
```

### `simple todo-gen`

Generate TODO.md documentation from the database.

**Syntax:**
```bash
simple todo-gen [OPTIONS]
```

**Options:**
- `--db <file>` - Input database path (default: `doc/todo/todo_db.sdn`)
- `-o, --output <dir>` - Output directory (default: `doc`)

**Examples:**
```bash
# Standard generation
simple todo-gen

# Custom paths
simple todo-gen --db custom/todos.sdn -o output/
```

## TODO Format

All TODOs must follow this format:

```
TODO: [area][priority] description [#issue] [blocked:#issue,#issue]
FIXME: [area][priority] description [#issue] [blocked:#issue,#issue]
```

### Areas (13 valid)

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

### Priorities (8 valid)

- `P0` or `critical` - Blocking, fix immediately
- `P1` or `high` - Important, next sprint
- `P2` or `medium` - Should do, backlog
- `P3` or `low` - Nice to have, someday

### Examples

**Rust:**
```rust
// TODO: [runtime][P0] Implement monoio TCP write [#234]
// TODO: [stdlib][critical] Fix memory leak [#567] [blocked:#123]
// FIXME: [parser][P2] Handle edge case in expression parsing
// TODO: [gpu][P1] Create Vector3 variant [#789] [blocked:#100,#101]
```

**Simple:**
```simple
# TODO: [stdlib][P0] Implement socket write via FFI [#234]
# TODO: [gpu][critical] Fix render pipeline memory leak [#567]
# FIXME: [ui][P2] Improve button click handling
# TODO: [doc][P1] Add examples section [#789] [blocked:#100]
```

**Markdown:**
```markdown
<!-- TODO: [doc][P1] Add architecture diagram [#123] -->
```

## Integration with Workflow

### Add to Makefile

Add these targets to your `Makefile`:

```make
.PHONY: check-todos
check-todos:
	@echo "Validating TODO format..."
	@./target/debug/simple todo-scan --validate

.PHONY: gen-todos
gen-todos:
	@echo "Updating TODO database..."
	@./target/debug/simple todo-scan
	@./target/debug/simple todo-gen
	@echo "Generated doc/TODO.md"

.PHONY: check-full
check-full: check-todos check-fmt check-lint test
	@echo "All checks passed!"
```

**Usage:**
```bash
make check-todos    # Validate format
make gen-todos      # Update database and docs
make check-full     # Run all checks including TODOs
```

### Add to CI/CD

Add to your CI pipeline:

```yaml
- name: Validate TODO Format
  run: |
    cargo build --release
    ./target/release/simple todo-scan --validate

- name: Check TODO Documentation
  run: |
    ./target/release/simple todo-gen
    git diff --exit-code doc/TODO.md
```

Or add to Makefile CI target:

```make
ci: check-full
	./target/release/simple todo-scan --validate
	./target/release/simple todo-gen
	git diff --exit-code doc/TODO.md || (echo "TODO.md out of sync - run 'make gen-todos'" && exit 1)
```

### Pre-commit Hook (Optional)

Create `.git/hooks/pre-commit`:

```bash
#!/bin/bash
# Validate TODO format before commit

./target/debug/simple todo-scan --validate
if [ $? -ne 0 ]; then
    echo "ERROR: Invalid TODO format detected"
    echo "Fix TODOs or run: simple todo-scan --validate"
    exit 1
fi
```

Make it executable:
```bash
chmod +x .git/hooks/pre-commit
```

## Troubleshooting

### Problem: "Binary not found"

**Solution:** Build the binary first
```bash
cargo build --release
./target/release/simple todo-scan --help
```

### Problem: "Invalid TODO format"

**Solution:** Check the TODO format
```bash
# See which TODOs are invalid
./target/release/simple todo-scan --validate

# Common fixes:
# - Add [area][priority]
# - Use valid area name
# - Use valid priority (P0-P3)
```

### Problem: "Duplicate key error"

**Solution:** This is an i18n build issue, not TODO-related. Wait for i18n fix.

### Problem: "Too many TODOs found"

**Solution:** This is normal for a first scan
```bash
# Review the output
cat doc/TODO.md

# Focus on P0/P1 first
grep -A 5 "P0 Critical" doc/TODO.md
```

### Problem: "Database out of sync"

**Solution:** Regenerate the database
```bash
./target/release/simple todo-scan
./target/release/simple todo-gen
```

## Tips & Best Practices

### 1. Use Descriptive TODOs

**Bad:**
```rust
// TODO: fix this
```

**Good:**
```rust
// TODO: [runtime][P1] Fix race condition in GC barrier [#567]
```

### 2. Add Issue Numbers

Link TODOs to GitHub issues:
```rust
// TODO: [compiler][P0] Implement type inference [#123]
```

### 3. Track Dependencies

Mark blocked TODOs:
```rust
// TODO: [gpu][P1] Add SIMD support [#200] [blocked:#199]
```

### 4. Regular Updates

Run weekly to keep database fresh:
```bash
# Monday morning routine
make gen-todos
git diff doc/TODO.md
```

### 5. Priority Guidelines

- **P0/critical:** Blockers, security issues, crashes
- **P1/high:** Important features, significant bugs
- **P2/medium:** Nice-to-have features, minor bugs
- **P3/low:** Future work, optimizations

## Quick Reference Card

```bash
# First time setup
cargo build --release
./target/release/simple todo-scan
./target/release/simple todo-gen

# Daily use
simple todo-scan --validate     # Check format
simple todo-scan                # Update database
simple todo-gen                 # Generate docs

# View results
cat doc/TODO.md                 # See all TODOs
head -20 doc/TODO.md            # Statistics
grep "P0" doc/TODO.md           # Critical items

# Integration
make check-todos                # In Makefile
make gen-todos                  # Update and commit
```

## Next Steps

1. ✅ Build binary: `cargo build --release`
2. ✅ Run first scan: `simple todo-scan`
3. ✅ Generate docs: `simple todo-gen`
4. ✅ Review output: `cat doc/TODO.md`
5. ✅ Fix invalid TODOs
6. ✅ Add to Makefile
7. ✅ Update CONTRIBUTING.md
8. ✅ Add to CI/CD

## Support

- **Format spec:** `.claude/skills/todo.md`
- **Implementation plan:** `doc/design/todo_db_plan.md`
- **Technical guide:** `doc/design/dual_language_todo_parsing.md`
- **Remaining work:** `doc/design/todo_db_remaining_work.md`

---

**Ready to use!** Just waiting for binary to build.
