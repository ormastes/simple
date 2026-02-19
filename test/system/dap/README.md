# DAP System Tests

Comprehensive system-level SSpec tests for the Debug Adapter Protocol (DAP) integration.

## Test Suite Overview

| Test File | Focus | Tests | Priority |
|-----------|-------|-------|----------|
| `breakpoint_management_spec.spl` | Breakpoint operations | 18 | P0 |
| `step_modes_spec.spl` | Stepping (Over/In/Out) | 22 | P0 |
| `stack_trace_spec.spl` | Stack frame tracking | 25 | P0 |
| `debug_state_spec.spl` | State management | 35 | P0 |
| `integration_spec.spl` | End-to-end workflows | 20 | P0 |
| **Total** | **All DAP features** | **120+** | **P0** |

## Running Tests

### Run All DAP Tests

```bash
simple test test/system/dap/
```

### Run Specific Test File

```bash
simple test test/system/dap/breakpoint_management_spec.spl
simple test test/system/dap/step_modes_spec.spl
simple test test/system/dap/stack_trace_spec.spl
simple test test/system/dap/debug_state_spec.spl
simple test test/system/dap/integration_spec.spl
```

### Run Tests With Tags

```bash
simple test --tag=dap
simple test --tag=system
```

## Test Coverage

### Breakpoint Management (18 tests)

**Features:**
- Adding single/multiple breakpoints
- Removing breakpoints
- Checking breakpoint existence
- Breakpoint hit detection
- Multiple files support
- Edge cases (line 0, large numbers, special chars)

**Key Tests:**
- ✅ Adds single breakpoint
- ✅ Adds multiple breakpoints in same file
- ✅ Removes specific breakpoint
- ✅ Checks breakpoint in correct file/line only
- ✅ Should break when at breakpoint location
- ✅ Handles special characters in file paths

### Step Modes (22 tests)

**Features:**
- Mode 0: Continue (no stepping)
- Mode 1: Step Over (same or lower depth)
- Mode 2: Step Into (any depth)
- Mode 3: Step Out (lower depth only)
- Depth tracking
- Mode transitions
- Interaction with breakpoints

**Key Tests:**
- ✅ Sets each mode correctly
- ✅ Breaks at same depth (StepOver)
- ✅ Does not break at higher depth (StepOver)
- ✅ Breaks at any depth (StepIn)
- ✅ Breaks only at lower depth (StepOut)
- ✅ Breakpoints override step modes

### Stack Trace (25 tests)

**Features:**
- Push/pop stack frames
- Stack depth tracking
- Stack trace generation
- Frame information (func, file, line, column)
- Recursive call tracking
- Deep call stacks
- Performance with many frames

**Key Tests:**
- ✅ Pushes single/multiple frames
- ✅ Pops frames in LIFO order
- ✅ Tracks depth correctly
- ✅ Generates trace with all frame info
- ✅ Tracks recursive calls separately
- ✅ Handles deep call stacks (100+ frames)

### Debug State (35 tests)

**Features:**
- Debug mode activation/deactivation
- Pause and continue
- Current location tracking
- State persistence
- Zero overhead when inactive
- Integration scenarios

**Key Tests:**
- ✅ Activates/deactivates debug mode
- ✅ Pauses and continues execution
- ✅ Tracks current file and line
- ✅ Maintains state across operations
- ✅ No overhead when inactive
- ✅ Full session lifecycle works

### Integration (20 tests)

**Features:**
- Complete debugging sessions
- Step through execution
- Recursive function debugging
- Multi-file debugging
- Breakpoint + stepping combined
- Error scenarios and recovery
- Performance/stress tests
- Real-world scenarios

**Key Tests:**
- ✅ Executes simple debugging session
- ✅ Steps through sequential code
- ✅ Steps over/into/out of functions
- ✅ Tracks recursive factorial calls
- ✅ Debugs across multiple files
- ✅ Handles 100+ breakpoints
- ✅ Debugs real-world programs

## Test Structure

All tests follow the SSpec format:

```simple
describe "Feature":
    """High-level feature description."""

    describe "Sub-feature":
        """Specific aspect of the feature."""

        it "does something specific":
            # Arrange
            debug_set_active(true)
            debug_add_breakpoint("test.spl", 10, 1)

            # Act
            debug_set_current_location("test.spl", 10, 0)

            # Assert
            expect(debug_should_break()).to(be_true())
```

## Expectations Used

| Expectation | Usage | Example |
|-------------|-------|---------|
| `be_true()` | Boolean true | `expect(active).to(be_true())` |
| `be_false()` | Boolean false | `expect(paused).to(be_false())` |
| `eq(value)` | Equality | `expect(mode).to(eq(0))` |
| `be_gt(n)` | Greater than | `expect(depth).to(be_gt(0))` |
| `be_gte(n)` | Greater/equal | `expect(depth).to(be_gte(5))` |
| `be_lt(n)` | Less than | `expect(count).to(be_lt(10))` |
| `contain(str)` | String contains | `expect(trace).to(contain("main"))` |

## FFI Functions Tested

### State Management
- `debug_is_active()` / `debug_set_active(bool)`
- `debug_pause()` / `debug_continue()` / `debug_is_paused()`

### Breakpoints
- `debug_add_breakpoint(file, line, id)`
- `debug_remove_breakpoint(file, line)`
- `debug_has_breakpoint(file, line)`
- `debug_should_break()`

### Location Tracking
- `debug_set_current_location(file, line, column)`
- `debug_current_file()`
- `debug_current_line()`

### Stepping
- `debug_set_step_mode(mode)` / `debug_get_step_mode()`
- `debug_set_step_start_depth(depth)` / `debug_get_step_start_depth()`

### Stack Management
- `debug_push_frame(func, file, line, column)`
- `debug_pop_frame()`
- `debug_stack_depth()`
- `debug_stack_trace()`

## Test Categories

### Unit-Level Tests
- Individual FFI function behavior
- Edge cases and boundary conditions
- Error handling

### Integration-Level Tests
- Multiple features working together
- Complete debugging workflows
- Real-world scenarios

### Performance Tests
- Many breakpoints (100+)
- Frequent location updates (1000+)
- Deep call stacks (100+ frames)
- Zero overhead when inactive

## Expected Results

All tests should **PASS** when:
- ✅ Rust FFI is built (`bootstrap_ffi_debug.rs`)
- ✅ Simple FFI wrappers are loaded (`src/lib/ffi/debug.spl`)
- ✅ Debug infrastructure is properly initialized

## Troubleshooting

### All Tests Fail

**Symptom:** All tests fail immediately

**Causes:**
1. FFI not compiled
2. FFI functions not linked

**Solution:**
```bash
# Rebuild with FFI
simple build --release
```

### Some Tests Fail

**Symptom:** Specific test categories fail

**Possible Issues:**
- Breakpoints: Check `debug_add_breakpoint()` implementation
- Step modes: Verify mode checking logic in `debug_should_break()`
- Stack: Check thread-local storage initialization
- State: Verify Mutex locking works correctly

### Performance Tests Slow

**Symptom:** Tests with 100+ operations are slow

**Expected:** Should complete in < 1 second
**If slow:** Check for unnecessary allocations or locking contention

## Continuous Integration

These tests should run on every commit:

```yaml
# .github/workflows/test.yml
test-dap:
  runs-on: ubuntu-latest
  steps:
    - uses: actions/checkout@v2
    - name: Build
      run: simple build
    - name: Test DAP
      run: simple test test/system/dap/
```

## Contributing

When adding new DAP features:

1. **Write tests first** (TDD approach)
2. **Follow SSpec format**
3. **Test edge cases**
4. **Include integration tests**
5. **Update this README**

### Test Template

```simple
describe "New Feature":
    """Description of new feature."""

    it "does the main thing":
        debug_set_active(true)
        # Test implementation
        expect(result).to(be_true())

    it "handles edge case":
        # Edge case test
        expect(true).to(be_true())
```

## See Also

- [DAP Debugging Guide](../../../doc/guide/dap_debugging_guide.md)
- [DAP Quick Reference](../../../doc/guide/dap_quick_reference.md)
- [SSpec Framework](../../../doc/guide/sspec_guide.md)
- [Integration Report](../../../doc/report/dap_integration_complete_2026-02-04.md)
