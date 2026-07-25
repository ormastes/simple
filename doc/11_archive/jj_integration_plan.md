# JJ Version Control Integration Plan

## Overview
Integrate Jujutsu (jj) version control to automatically store successful build states, enabling fast rollback and build state exploration.

## Goals
1. Auto-snapshot on successful compilation
2. Auto-snapshot on successful test runs
3. Store build metadata in commit messages
4. Enable quick rollback to last working state
5. Track test state progression (deferred until test framework ready)

## Architecture

### Components

#### 1. JJ State Manager (`src/driver/src/jj_state.rs`)
```rust
pub struct JjStateManager {
    enabled: bool,
    repo_path: PathBuf,
}

impl JjStateManager {
    pub fn new() -> Result<Self>;
    pub fn is_enabled() -> bool;
    pub fn snapshot_build_success(&self, metadata: BuildMetadata) -> Result<()>;
    pub fn snapshot_test_success(&self, metadata: TestMetadata) -> Result<()>;
    pub fn get_last_working_state(&self) -> Result<Option<String>>;
}
```

#### 2. Build Metadata
```rust
pub struct BuildMetadata {
    pub timestamp: DateTime<Utc>,
    pub duration_ms: u64,
    pub artifacts: Vec<PathBuf>,
    pub target: String,
    pub mode: BuildMode, // Debug, Release
}

pub struct TestMetadata {
    pub timestamp: DateTime<Utc>,
    pub duration_ms: u64,
    pub total_tests: usize,
    pub passed: usize,
    pub failed: usize,
    pub ignored: usize,
    pub test_level: TestLevel, // Unit, IT, System, Env
}
```

#### 3. Makefile Integration
```makefile
# Auto-snapshot on successful builds
build-snapshot: build
	@if [ -f .jj/repo ]; then \
		simple snapshot-build --success; \
	fi

# Auto-snapshot on test success
test-snapshot: test
	@if [ $$? -eq 0 ] && [ -f .jj/repo ]; then \
		simple snapshot-test --level=all --success; \
	fi
```

## Implementation Phases

### Phase 1: JJ Initialization (Setup)
**Files:** `.jj/`, `Makefile`, `doc/jj_usage.md`
**Tests:** Manual verification
**Duration:** 15 minutes

**Tasks:**
1. Initialize jj co-located with git: `jj git init --colocate`
2. Create `.jjignore` file
3. Add jj setup documentation
4. Update `.gitignore` to exclude jj state

**Deliverables:**
- Working jj repo co-located with git
- Documentation on jj workflow
- Ignore rules for build artifacts

### Phase 2: Core JJ State Manager (TDD)
**Files:** `src/driver/src/jj_state.rs`, tests
**Tests:** Unit tests (15+ tests)
**Duration:** 2 hours

**Tests to Write:**
```rust
#[test] fn jj_state_manager_detects_repo()
#[test] fn jj_state_manager_disabled_when_no_repo()
#[test] fn snapshot_build_creates_commit()
#[test] fn snapshot_test_creates_commit()
#[test] fn build_metadata_serializes_correctly()
#[test] fn test_metadata_serializes_correctly()
#[test] fn get_last_working_state_returns_latest()
#[test] fn snapshot_includes_timestamp()
#[test] fn snapshot_includes_duration()
#[test] fn snapshot_includes_artifacts()
#[test] fn snapshot_message_format_correct()
#[test] fn multiple_snapshots_track_history()
#[test] fn snapshot_fails_gracefully_no_repo()
#[test] fn snapshot_preserves_git_state()
#[test] fn snapshot_is_idempotent()
```

**Implementation:**
1. Create `JjStateManager` struct
2. Implement repo detection
3. Implement snapshot creation via `jj commit`
4. Implement metadata serialization
5. Add error handling
6. Write all tests (TDD)

### Phase 3: Build Integration (TDD)
**Files:** `src/driver/src/runner.rs`, `Makefile`, tests
**Tests:** Integration tests (8+ tests)
**Duration:** 1.5 hours

**Tests to Write:**
```rust
#[test] fn runner_snapshots_on_compile_success()
#[test] fn runner_skips_snapshot_on_compile_fail()
#[test] fn runner_includes_build_duration()
#[test] fn runner_includes_artifact_list()
#[test] fn runner_snapshot_disabled_without_jj()
#[test] fn makefile_build_snapshot_works()
#[test] fn snapshot_message_contains_metadata()
#[test] fn multiple_builds_create_history()
```

**Implementation:**
1. Add `--snapshot` flag to runner
2. Hook into compilation success path
3. Collect build metadata
4. Call `JjStateManager::snapshot_build_success()`
5. Add Makefile targets
6. Write all tests (TDD)

### Phase 4: Test Integration (TDD)
**Files:** `src/driver/src/runner.rs`, `Makefile`, tests
**Tests:** Integration tests (10+ tests)
**Duration:** 1.5 hours

**Tests to Write:**
```rust
#[test] fn runner_snapshots_on_all_tests_pass()
#[test] fn runner_skips_snapshot_on_test_fail()
#[test] fn snapshot_includes_test_counts()
#[test] fn snapshot_includes_test_level()
#[test] fn snapshot_includes_duration()
#[test] fn makefile_test_snapshot_unit_works()
#[test] fn makefile_test_snapshot_it_works()
#[test] fn makefile_test_snapshot_system_works()
#[test] fn makefile_test_snapshot_all_works()
#[test] fn test_snapshot_disabled_without_jj()
```

**Implementation:**
1. Add `--snapshot-on-success` to test runner
2. Hook into test completion
3. Collect test metadata (counts, level, duration)
4. Call `JjStateManager::snapshot_test_success()`
5. Add Makefile targets
6. Write all tests (TDD)

### Phase 5: CLI Commands (TDD)
**Files:** `src/driver/src/main.rs`, tests
**Tests:** System tests (6+ tests)
**Duration:** 1 hour

**Commands to Add:**
```bash
simple snapshot-build --success
simple snapshot-test --level=unit --success
simple last-working-state
simple list-snapshots
simple rollback-to <snapshot>
```

**Tests to Write:**
```rust
#[test] fn cli_snapshot_build_creates_commit()
#[test] fn cli_snapshot_test_creates_commit()
#[test] fn cli_last_working_state_shows_latest()
#[test] fn cli_list_snapshots_shows_history()
#[test] fn cli_rollback_restores_state()
#[test] fn cli_snapshot_fails_gracefully_no_jj()
```

### Phase 6: Documentation & Polish
**Files:** `doc/jj_usage.md`, `CLAUDE.md`, `README.md`
**Duration:** 1 hour

**Documentation:**
1. Usage guide (`doc/jj_usage.md`)
2. Workflow examples
3. Troubleshooting
4. Update CLAUDE.md with JJ section
5. Update README.md with JJ feature

### Phase 7: Test State Storage (DEFERRED)
**Status:** Pending test framework implementation
**Files:** TBD
**Duration:** TBD (depends on test framework)

**Deferred Features:**
1. Test state serialization (pass/fail/ignored per test)
2. Test progression tracking (flaky test detection)
3. Test timing analysis
4. Coverage progression tracking

**Reason for Deferral:**
Current test framework uses standard `cargo test` which doesn't expose individual test state easily. Need custom test framework integration first.

## Commit Message Format

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

```makefile
# JJ Integration
jj-init:
	jj git init --colocate
	@echo "JJ repo initialized (co-located with git)"

# Auto-snapshot targets
build-snapshot: build
	@if [ -f .jj/repo ]; then \
		simple snapshot-build --success; \
	fi

test-snapshot: test
	@if [ $$? -eq 0 ] && [ -f .jj/repo ]; then \
		simple snapshot-test --level=all --success; \
	fi

test-unit-snapshot: test-unit
	@if [ $$? -eq 0 ] && [ -f .jj/repo ]; then \
		simple snapshot-test --level=unit --success; \
	fi

# Convenience targets
check-snapshot: check
	@if [ $$? -eq 0 ] && [ -f .jj/repo ]; then \
		simple snapshot-build --success; \
		simple snapshot-test --level=all --success; \
	fi

# State management
last-working:
	simple last-working-state

list-snapshots:
	jj log --limit 20 -r 'description(~"Build Success|Tests Passed")'

rollback:
	@echo "Usage: make rollback-to SNAPSHOT=<id>"

rollback-to:
	@if [ -z "$(SNAPSHOT)" ]; then \
		echo "Error: SNAPSHOT not specified"; \
		exit 1; \
	fi
	jj edit $(SNAPSHOT)
```

## File: `.jjignore`

```
# Build artifacts
target/
*.smf
*.o
*.a
*.so
*.dylib
*.dll

# IDE
.vscode/
.idea/
*.swp
*.swo

# Logs
log/
*.log

# Coverage
*.profraw
*.profdata

# Temporary
tmp/
temp/
```

## Dependencies

```toml
# Add to src/driver/Cargo.toml
[dependencies]
chrono = "0.4"
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
```

## Success Metrics

1. **Phase 1:** JJ repo initialized ✅
2. **Phase 2:** 15+ unit tests passing ✅
3. **Phase 3:** 8+ integration tests passing ✅
4. **Phase 4:** 10+ integration tests passing ✅
5. **Phase 5:** 6+ system tests passing ✅
6. **Phase 6:** Complete documentation ✅
7. **Overall:** All 2507 workspace tests still passing ✅

## Timeline

| Phase | Duration | Dependencies |
|-------|----------|--------------|
| 1. Setup | 15 min | None |
| 2. Core | 2 hours | Phase 1 |
| 3. Build | 1.5 hours | Phase 2 |
| 4. Test | 1.5 hours | Phase 2 |
| 5. CLI | 1 hour | Phases 2-4 |
| 6. Docs | 1 hour | Phases 1-5 |
| **Total** | **~7.5 hours** | |

## Rollout Strategy

1. **Development:** Implement all phases in order
2. **Testing:** TDD throughout (39+ tests minimum)
3. **Validation:** Manual testing of workflow
4. **Documentation:** Complete before merge
5. **Commit:** Single atomic commit with all phases

## Benefits

1. **Fast Rollback:** Instant return to last working state
2. **Build History:** Track successful build progression
3. **Test History:** Track test suite health
4. **Debugging:** Compare working vs broken states
5. **CI/CD:** Enable snapshot-based deployment
6. **Development Velocity:** Less fear of breaking changes

## Risks & Mitigations

| Risk | Impact | Mitigation |
|------|--------|-----------|
| JJ not installed | High | Graceful degradation, clear error messages |
| Performance overhead | Medium | Make snapshots opt-in, async execution |
| Disk space usage | Medium | Document cleanup strategy, `jj gc` |
| Git conflict | Low | Co-located mode tested, documentation |
| Test framework coupling | Medium | Defer test state storage to Phase 7 |

## Future Enhancements (Phase 7+)

1. Test state progression tracking
2. Flaky test detection
3. Performance regression detection
4. Coverage progression graphs
5. Auto-bisect on test failures
6. Snapshot comparison tools
7. Cloud backup of snapshots
8. Team snapshot sharing

## Implementation Order (TDD)

```
1. Write Phase 2 unit tests → Implement → Green
2. Write Phase 3 integration tests → Implement → Green
3. Write Phase 4 integration tests → Implement → Green
4. Write Phase 5 system tests → Implement → Green
5. Phase 1 (setup, no tests needed)
6. Phase 6 (documentation)
7. Run full test suite (2507+ tests)
8. Commit all changes atomically
```

## Notes

- All implementation follows TDD (test-first)
- Minimum 39 tests (15+8+10+6)
- Phase 7 deferred until test framework ready
- All features opt-in (graceful degradation)
- Co-located mode preserves git workflow
- Documentation-first for complex features
