# TODO System - Makefile Integration (Ready to Add)

**Status:** Ready to copy-paste into Makefile
**When:** After binary builds successfully

## Makefile Additions

Add these targets to your `Makefile`:

```make
#
# TODO Database Management
#

.PHONY: check-todos
check-todos:
	@echo "Validating TODO format..."
	@./target/debug/simple todo-scan --validate || (echo "ERROR: Invalid TODO format found. Run 'simple todo-scan --validate' for details." && exit 1)
	@echo "✓ All TODOs are properly formatted"

.PHONY: gen-todos
gen-todos:
	@echo "Updating TODO database..."
	@./target/debug/simple todo-scan
	@./target/debug/simple todo-gen
	@echo "✓ Generated doc/TODO.md"

.PHONY: todos
todos: gen-todos
	@cat doc/TODO.md | head -30

.PHONY: todos-p0
todos-p0:
	@echo "Critical (P0) TODOs:"
	@grep -A 3 "P0 Critical" doc/TODO.md || echo "No P0 TODOs found!"

.PHONY: todos-stats
todos-stats:
	@echo "TODO Statistics:"
	@head -20 doc/TODO.md
```

## Update Existing Targets

### Option 1: Add to existing `check-full`

If you already have a `check-full` target:

```make
check-full: check-fmt check-lint check-todos test
	@echo "✓ All checks passed!"
```

### Option 2: Create new comprehensive check

```make
check-all: check-fmt check-lint check-todos test coverage
	@echo "✓ All checks passed with coverage!"
```

### Option 3: Separate TODO target

Keep TODO checks separate:

```make
check: check-fmt check-lint test

check-with-todos: check check-todos
	@echo "✓ All checks passed including TODOs!"
```

## CI/CD Integration

Add to your CI target:

```make
ci: check-full
	@echo "Running CI checks..."
	@./target/release/simple todo-scan --validate
	@./target/release/simple todo-gen
	@git diff --exit-code doc/TODO.md || (echo "❌ TODO.md is out of sync. Run 'make gen-todos' and commit the changes." && exit 1)
	@echo "✓ CI checks passed!"
```

## Help Text

Add TODO commands to your help:

```make
help:
	@echo "Simple Language Compiler - Make Targets"
	@echo ""
	@echo "Build:"
	@echo "  make                  - Build debug binary"
	@echo "  make release          - Build release binary"
	@echo ""
	@echo "Testing:"
	@echo "  make test             - Run tests"
	@echo "  make check            - Run fmt + lint + test"
	@echo "  make check-full       - Run all checks including TODOs"
	@echo ""
	@echo "TODO Management:"
	@echo "  make check-todos      - Validate TODO format"
	@echo "  make gen-todos        - Update TODO database and docs"
	@echo "  make todos            - Show TODO summary"
	@echo "  make todos-p0         - Show critical TODOs"
	@echo "  make todos-stats      - Show TODO statistics"
	@echo ""
	@echo "Documentation:"
	@echo "  make docs             - Generate documentation"
	@echo "  make feature-gen      - Generate feature docs"
	@echo "  make task-gen         - Generate task docs"
	@echo ""
```

## Complete Example

Here's a complete Makefile section with all TODO-related targets:

```make
# ====================
# TODO Management
# ====================

.PHONY: check-todos
check-todos:
	@echo "Validating TODO format..."
	@./target/debug/simple todo-scan --validate || (echo "ERROR: Invalid TODO format found" && exit 1)
	@echo "✓ All TODOs are properly formatted"

.PHONY: gen-todos
gen-todos:
	@echo "Updating TODO database..."
	@./target/debug/simple todo-scan
	@./target/debug/simple todo-gen
	@echo "✓ Generated doc/TODO.md"

.PHONY: todos
todos: gen-todos
	@echo "TODO Summary:"
	@echo ""
	@head -30 doc/TODO.md

.PHONY: todos-p0
todos-p0:
	@echo "==================================="
	@echo "   Critical (P0) TODOs"
	@echo "==================================="
	@grep -A 5 "## P0 Critical TODOs" doc/TODO.md | tail -n +2 || echo "✓ No P0 TODOs found!"

.PHONY: todos-p1
todos-p1:
	@echo "==================================="
	@echo "   High Priority (P1) TODOs"
	@echo "==================================="
	@grep -A 5 "## P1 High Priority TODOs" doc/TODO.md | tail -n +2 || echo "No P1 TODOs found"

.PHONY: todos-stats
todos-stats:
	@echo "==================================="
	@echo "   TODO Statistics"
	@echo "==================================="
	@head -20 doc/TODO.md

.PHONY: todos-by-area
todos-by-area:
	@echo "TODOs by Area:"
	@grep "^| runtime" doc/TODO.md || true
	@grep "^| codegen" doc/TODO.md || true
	@grep "^| compiler" doc/TODO.md || true
	@grep "^| stdlib" doc/TODO.md || true
	@grep "^| gpu" doc/TODO.md || true

.PHONY: todos-clean
todos-clean:
	@echo "Cleaning stale TODO data..."
	@rm -f doc/todo/todo_db.sdn.bak
	@echo "✓ Cleaned"

# ====================
# Combined Checks
# ====================

.PHONY: check
check: check-fmt check-lint test
	@echo "✓ Basic checks passed"

.PHONY: check-full
check-full: check check-todos
	@echo "✓ All checks passed!"

.PHONY: check-ci
check-ci: check-full
	@./target/release/simple todo-scan --validate
	@./target/release/simple todo-gen
	@git diff --exit-code doc/TODO.md || (echo "❌ TODO.md out of sync" && exit 1)
	@echo "✓ CI checks passed!"
```

## Usage Examples

```bash
# Validate TODO format
make check-todos

# Update TODO database and docs
make gen-todos

# Show TODO summary
make todos

# Show critical TODOs only
make todos-p0

# Show statistics
make todos-stats

# Full check including TODOs
make check-full

# CI check
make check-ci
```

## Install Instructions

### Step 1: Backup current Makefile

```bash
cp Makefile Makefile.backup
```

### Step 2: Add TODO targets

Open `Makefile` and add the targets from above. Suggested location:

```make
# ... existing targets ...

# ====================
# TODO Management
# ====================

# ... paste TODO targets here ...

# ... rest of Makefile ...
```

### Step 3: Update check-full target

Find your existing `check-full` (or `check`) target and add `check-todos`:

```make
# Before
check-full: check-fmt check-lint test

# After
check-full: check-fmt check-lint check-todos test
```

### Step 4: Test it

```bash
make check-todos
make gen-todos
make todos
```

## Optional: Watch Mode

Add a watch target that auto-updates TODOs:

```make
.PHONY: todos-watch
todos-watch:
	@echo "Watching for TODO changes (Ctrl+C to stop)..."
	@while true; do \
		./target/debug/simple todo-scan --validate && \
		sleep 5; \
	done
```

Usage:
```bash
make todos-watch
```

## Integration Checklist

- [ ] Add TODO management section to Makefile
- [ ] Add `check-todos` target
- [ ] Add `gen-todos` target
- [ ] Add `todos` summary target
- [ ] Update `check-full` to include `check-todos`
- [ ] Update help text
- [ ] Test all new targets
- [ ] Commit changes

## After Installation

Run these commands to verify:

```bash
# Should validate TODOs
make check-todos

# Should generate docs
make gen-todos

# Should show summary
make todos

# Should pass full check
make check-full
```

If all work, you're done! The TODO system is fully integrated.
