---
name: verify-work
description: Post-implementation verification checklist for tests, lint, coverage, docs, and VCS state
---

# Post-Implementation Verification

## Quick Checklist

Run after completing any implementation task:

### 1. Tests Pass
```bash
bin/simple test                      # All tests
bin/simple test path/to/spec.spl     # Changed file tests
```

### 2. Lint Clean
```bash
bin/simple build lint                # Linter
bin/simple build fmt                 # Formatter
bin/simple build check               # All checks
```

### 3. No Regressions
```bash
bin/simple test --only-slow          # Slow/integration tests
```

### 4. Coverage (if applicable)
```bash
bin/simple test --coverage           # Coverage report
```

### 5. Documentation Updated
- [ ] Docstrings on new public APIs
- [ ] CLAUDE.md updated if conventions changed
- [ ] Skill files updated if workflow changed

### 6. VCS State Clean
```bash
jj status                            # Check working copy
jj diff --stat                       # Review changes
```

### 7. TODO Tracking
```bash
bin/simple todo-scan                 # Update TODO tracking
```

### 8. Duplication Check
```bash
bin/simple duplicate-check src/      # Check for code duplication
```

## When to Run Full vs Quick

| Scope | Checks |
|-------|--------|
| Small edit (< 10 lines) | Tests + Lint |
| Feature addition | Full checklist |
| Bug fix | Tests + Lint + Regression |
| Refactor | Full checklist + Duplication |

## Automated Checks

The Stop hooks automatically check for:
- Uncommitted changes (`completion-guard.sh`)
- New TODO/FIXME comments (`todo-check.sh`)
- Modified Rust files (`pure-simple-guard.sh`)
- Session change summary (`session-summary.sh`)
