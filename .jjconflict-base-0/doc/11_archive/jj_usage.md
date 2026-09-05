# Jujutsu (JJ) Version Control Integration

## Overview

Simple Language uses [Jujutsu (jj)](https://github.com/martinvonz/jj) for automatic build state management. JJ runs co-located with Git, providing fast snapshots of successful builds and test runs.

## Setup

### Installation

```bash
# Install jj
cargo install jj-cli

# Verify installation
jj --version
```

### Repository Setup

JJ is already initialized in co-located mode with Git:

```bash
# Check status
jj log --limit 5

# Track main branch
jj bookmark track main@origin
```

## Features

### 1. Automatic Build Snapshots

Every successful build creates a snapshot:

```bash
# Manual snapshot
make build-snapshot

# Automatic (via check)
make check-snapshot
```

**Snapshot includes:**
- Build duration
- Artifacts created
- Target architecture
- Build mode (Debug/Release)
- Timestamp

### 2. Automatic Test Snapshots

Every successful test run creates a snapshot:

```bash
# Snapshot after all tests pass
make test-snapshot

# Snapshot after specific test level
make test-unit-snapshot
make test-it-snapshot
make test-system-snapshot
```

**Snapshot includes:**
- Test counts (total, passed, failed, ignored)
- Test level (Unit, IT, System, Env)
- Test duration
- Timestamp

### 3. State Management

```bash
# View snapshot history
make list-snapshots
jj log -r 'description(~"Build Success|Tests Passed")'

# Get last working state
make last-working
simple last-working-state

# Rollback to specific snapshot
make rollback-to SNAPSHOT=abc123
jj edit abc123
```

## Workflow

### Normal Development

```bash
# Make changes
vim src/compiler/src/codegen/llvm.rs

# Build and test (auto-snapshots on success)
make check-snapshot

# View history
jj log --limit 10
```

### After Breaking Changes

```bash
# Oh no, tests are failing!
cargo test  # ❌ Failures

# Find last working state
make last-working
# Output: "Last working state: abc123 (2 hours ago)"

# Rollback
make rollback-to SNAPSHOT=abc123

# Verify it works
cargo test  # ✅ All pass

# Compare differences
jj diff --from abc123 --to @
```

### Exploring Build History

```bash
# List all successful builds
jj log -r 'description(~"Build Success")'

# List all test successes
jj log -r 'description(~"Tests Passed")'

# Show specific snapshot
jj show abc123

# Compare two snapshots
jj diff --from abc123 --to def456
```

## Commit Message Formats

### Build Success

```
🏗️  Build Success

Duration: 3.2s
Mode: Release
Target: x86_64-unknown-linux-gnu
Artifacts: 
  - target/release/simple (2.3 MB)
  - target/release/libsimple_runtime.so (1.1 MB)

Timestamp: 2025-12-14T00:36:13Z
```

### Test Success

```
✅ Tests Passed: All

Level: Unit
Total: 2507 tests
Passed: 2507
Failed: 0
Ignored: 3
Duration: 12.4s

Timestamp: 2025-12-14T00:36:25Z
```

## Makefile Targets

```bash
# JJ initialization (already done)
make jj-init

# Build with snapshot
make build-snapshot

# Test with snapshot (all levels)
make test-snapshot

# Test specific level with snapshot
make test-unit-snapshot

# Full check with snapshot
make check-snapshot

# View snapshots
make list-snapshots

# Get last working state
make last-working

# Rollback to snapshot
make rollback-to SNAPSHOT=<id>
```

## CLI Commands

```bash
# Snapshot successful build
simple snapshot-build --success

# Snapshot successful test run
simple snapshot-test --level=unit --success
simple snapshot-test --level=all --success

# Get last working state
simple last-working-state

# List snapshots (uses jj)
simple list-snapshots
```

## JJ vs Git

### Co-Located Mode

JJ and Git work together:

- **JJ:** Fast local snapshots, easy undo, change-based workflow
- **Git:** Remote collaboration, standard ecosystem

All Git commands still work:

```bash
git status
git commit -m "feature: add LLVM backend"
git push origin main
```

JJ operations don't interfere with Git.

### When to Use Each

| Task | Use | Reason |
|------|-----|--------|
| Local experiments | JJ | Fast undo, no commit messages needed |
| Automatic snapshots | JJ | No manual intervention |
| Remote collaboration | Git | Standard ecosystem |
| Pull requests | Git | GitHub/GitLab workflows |
| Rollback builds | JJ | Instant, no checkout needed |
| Public history | Git | Clean, squashed commits |

## Best Practices

### 1. Let Automation Work

Don't manually create snapshots unless needed:

```bash
# ✅ Good: Let make handle it
make check-snapshot

# ❌ Bad: Manual snapshots for routine work
simple snapshot-build --success
```

### 2. Use Snapshots for Exploration

```bash
# Try experimental change
vim src/compiler/src/codegen/llvm.rs
make check-snapshot  # Snapshot working state

# Experiment
vim src/compiler/src/codegen/llvm.rs
cargo test  # Might fail, no problem

# Rollback if needed
make last-working
```

### 3. Clean Up Old Snapshots

```bash
# JJ automatically garbage collects
jj gc

# Manual cleanup (if needed)
jj log --limit 100  # Review old snapshots
jj abandon <old-snapshot-id>
```

### 4. Preserve Git Workflow

```bash
# Keep Git commits clean
git add src/compiler/src/codegen/llvm.rs
git commit -m "feat: add LLVM IR generation"

# JJ snapshots are separate
jj log --limit 5  # Shows automatic snapshots
```

## Troubleshooting

### JJ Not Found

```bash
# Install jj
cargo install jj-cli

# Verify
jj --version
```

### Snapshots Not Created

```bash
# Check if jj is enabled
ls -la .jj/

# Re-initialize if needed
make jj-init
```

### Too Many Snapshots

```bash
# Garbage collect
jj gc

# Abandon old snapshots
jj abandon <snapshot-id>
```

### JJ Status Fails

```bash
# Check current directory
cd /path/to/simple

# Verify jj repo exists
ls -la .jj/

# Check jj log
jj log --limit 3
```

## Advanced Usage

### Custom Snapshot Messages

```bash
# Manual snapshot with custom message
jj commit -m "💡 Experimental LLVM optimization working"
```

### Bisecting Failures

```bash
# Find when tests started failing
jj log -r 'description(~"Tests Passed")' --limit 20

# Test each snapshot
jj edit <snapshot-id>
cargo test
```

### Comparing Performance

```bash
# Benchmark current state
cargo bench

# Go back to previous snapshot
jj edit <old-snapshot>
cargo bench

# Compare results
jj diff --from <old> --to @
```

## Integration with CI/CD

### GitHub Actions

```yaml
- name: Snapshot successful build
  if: success()
  run: |
    if [ -f .jj/repo ]; then
      make build-snapshot
    fi
```

### Local Pre-Commit

```bash
# .git/hooks/pre-commit
#!/bin/bash
make check-snapshot
```

## Future Features (Planned)

1. **Test State Storage:** Track individual test pass/fail state
2. **Flaky Test Detection:** Identify tests that sometimes fail
3. **Performance Regression:** Auto-detect slow builds/tests
4. **Coverage Progression:** Track coverage over time
5. **Cloud Backup:** Optional snapshot backup to cloud storage
6. **Team Sharing:** Share snapshots with team members

## References

- [Jujutsu Documentation](https://martinvonz.github.io/jj/)
- [JJ vs Git Comparison](https://martinvonz.github.io/jj/latest/git-comparison/)
- [Simple Language - JJ Integration Plan](./jj_integration_plan.md)

## Support

For issues with JJ integration:

1. Check this documentation
2. Run `make last-working` to find last good state
3. Check `doc/jj_integration_plan.md` for implementation details
4. File an issue on GitHub with JJ logs

---

**Note:** JJ integration is completely optional. The build system works fine without it, but snapshots provide valuable rollback capability and build history.
