# JJ Version Control Integration Plan

**Status:** In Progress (67% Complete)  
**Priority:** High (Developer Tooling)  
**Goal:** Auto-snapshot successful builds and test runs to JJ (Jujutsu VCS)

## Overview

Integrate with Jujutsu (JJ) version control to automatically create snapshots of successful builds and test runs, enabling easy rollback to last working state.

## Completed (8/12 Tasks)

### 1. ✅ Core State Management
- **File:** `src/driver/src/jj_state.rs`
- **Features:**
  - JjStateManager - Core state management with JJ CLI integration
  - BuildMetadata - Track build success, duration, artifacts, mode
  - TestMetadata - Track test results, duration, pass/fail/ignored counts
  - Automatic snapshot creation on build/test success
  - Last working state retrieval

### 2. ✅ Unit Tests (2 passing)
- Display methods for metadata structures
- Located in `jj_state.rs`

### 3. ✅ Integration Tests (15/15 passing)
- **File:** `src/driver/tests/jj_state_tests.rs`
- **Coverage:**
  - Build snapshots (8 tests)
  - Test snapshots (4 tests)
  - Edge cases and idempotency (3 tests)

### 4. ✅ Event System Infrastructure (12 tests passing)
- **Files:**
  - `src/driver/src/jj/event.rs` - BuildEvent and BuildState types
  - `src/driver/src/jj/store.rs` - StateStore for persistent build history
  - `src/driver/src/jj/jj.rs` - JJConnector for JJ CLI integration
  - `src/driver/src/jj/message.rs` - MessageFormatter for user-facing messages

**Event Types:**
- CompilationStarted
- CompilationSucceeded
- CompilationFailed
- TestRunStarted
- TestRunSucceeded
- TestRunFailed

### 5. ✅ CLI Integration
- **Added:** `--snapshot` flag to `simple compile` command
- **Feature:** Automatic BuildEvent tracking
- **Output:**
  ```bash
  simple compile app.spl --snapshot
  # Compiled app.spl -> app.smf
  # 📸 Updated JJ change description with build state (commit: abc123...)
  ```

## Remaining (4/12 Tasks)

### 6. ⏳ Wire Test Success Tracking
**Status:** Blocked (pending test framework)

**Task:** Integrate TestEvent capture into test runner
- Add `--snapshot` flag to `simple test` command
- Track TestRunStarted/Succeeded/Failed events
- Store test state via JJConnector

**Dependencies:**
- BDD Spec framework runner (Sprint 2)
- CLI test command infrastructure

### 7. ⏳ System Tests
**Status:** Planned

**Task:** End-to-end snapshot workflow tests
- Test compile → snapshot → rollback workflow
- Test test → snapshot → rollback workflow
- Verify JJ change descriptions
- Verify state persistence

**Test Scenarios:**
1. Successful build creates snapshot
2. Failed build does not create snapshot
3. Multiple snapshots track history
4. Rollback restores working state

**File:** `src/driver/tests/jj_system_tests.rs` (to create)

### 8. ⏳ Documentation
**Status:** Planned

**Task:** User guide and examples
- Usage guide for `--snapshot` flag
- JJ integration overview
- Configuration options
- Troubleshooting guide

**Files to Create:**
- `doc/jj_integration.md` - User guide
- Examples in `doc/examples/jj_workflow.md`

### 9. 🔒 Test State Storage
**Status:** Deferred

**Reason:** Pending test framework setup
**Dependencies:**
- BDD Spec framework complete
- Test runner infrastructure
- Test result persistence design

## Implementation Details

### Build State Tracking

```rust
pub struct BuildState {
    pub commit_id: Option<String>,
    pub events: Vec<BuildEvent>,
    pub compilation_success: bool,
    pub test_success: Option<bool>,
    pub timestamp: SystemTime,
}
```

### JJ CLI Integration

```rust
pub struct JJConnector {
    repo_root: PathBuf,
    state_store: StateStore,
}

impl JJConnector {
    pub fn describe_with_state(&self, state: &BuildState) -> io::Result<()>
    pub fn store_state(&self, state: BuildState) -> io::Result<()>
    pub fn load_current_states(&self) -> io::Result<Vec<BuildState>>
    pub fn has_successful_build(&self) -> io::Result<bool>
}
```

### State Persistence

**Location:** `.jj/.simple/build_states/`
**Format:** JSON per commit ID

```json
{
  "commit_id": "abc123...",
  "events": [
    {
      "CompilationStarted": {
        "timestamp": "2025-12-14T03:00:00Z",
        "files": ["app.spl"]
      }
    },
    {
      "CompilationSucceeded": {
        "timestamp": "2025-12-14T03:00:05Z",
        "duration_ms": 5000
      }
    }
  ],
  "compilation_success": true,
  "timestamp": "2025-12-14T03:00:05Z"
}
```

## CLI Usage

### Current (Implemented)

```bash
# Compile with snapshot
simple compile app.spl --snapshot

# Cross-compile with snapshot
simple compile app.spl --target aarch64 --snapshot
```

### Future (Planned)

```bash
# Run tests with snapshot
simple test --snapshot

# Run tests with coverage and snapshot
simple test --coverage --snapshot

# Check last working state
simple jj status

# Rollback to last working build
jj undo
```

## Architecture

```
Driver (main.rs)
    ├── compile_file() - Tracks BuildEvents
    │   ├── BuildEvent::CompilationStarted
    │   ├── [compilation]
    │   └── BuildEvent::CompilationSucceeded/Failed
    │
    ├── JJConnector
    │   ├── describe_with_state() - Update JJ change description
    │   ├── store_state() - Persist build state
    │   └── load_current_states() - Retrieve history
    │
    └── StateStore
        ├── .jj/.simple/build_states/{commit_id}.json
        └── Indexed by commit ID
```

## Testing Strategy

### Unit Tests (2 passing)
- Metadata display formatting
- State structure validation

### Integration Tests (15 passing)
- Build snapshot creation
- Test snapshot creation
- State persistence and retrieval
- Idempotency checks
- Edge case handling

### System Tests (Planned)
- End-to-end workflow
- JJ CLI interaction
- Rollback scenarios
- Multi-commit history

## Dependencies

**External:**
- Jujutsu (jj) CLI installed
- JJ repository initialized (`jj git init` or `jj init`)

**Internal:**
- BDD Spec framework (for test tracking)
- Test runner infrastructure
- CLI command framework

## Timeline

**Completed:** ~8 hours (67%)
**Remaining:** ~4 hours (33%)

**Breakdown:**
- Test tracking integration: 1 hour (blocked)
- System tests: 2 hours
- Documentation: 1 hour

**Total Estimate:** 12 hours

## Benefits

### For Developers
- Automatic build/test history tracking
- Easy rollback to last working state
- No manual snapshot management
- Clear build metadata in commits

### For Teams
- Shared build history via JJ
- Easy identification of breaking changes
- Audit trail for builds and tests
- Reproducible builds

### For CI/CD
- Automated snapshot creation
- Build state persistence
- Integration with version control
- Machine-readable build history

## Future Enhancements

1. **Coverage Integration**
   - Track coverage metrics with builds
   - Snapshot coverage reports
   - Historical coverage trends

2. **Benchmark Integration**
   - Track performance metrics
   - Snapshot benchmark results
   - Performance regression detection

3. **Artifact Management**
   - Store build artifacts in JJ
   - Reference artifacts by commit
   - Artifact deduplication

4. **Web UI**
   - Visualize build history
   - Interactive rollback
   - Build comparison

## See Also

- `doc/llm_friendly.md` - LLM-friendly features overview
- `doc/guides/test.md` - Test policy and coverage rules
- JJ Documentation: https://github.com/martinvonz/jj
