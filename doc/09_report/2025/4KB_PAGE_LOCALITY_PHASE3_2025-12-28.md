# 4KB Page Locality - Phase 3 Complete

**Date:** 2025-12-28
**Phase:** 3 of 5 - Test Framework Layout Recording
**Features:** #2020-#2029 (10 features)
**Cumulative Progress:** 29/50 features (58%)

## Summary

Phase 3 implements the test framework layout recording infrastructure that captures function execution patterns during test runs. This data drives the layout optimization by identifying which functions are called during startup vs steady-state execution.

## Features Implemented (#2020-#2029)

### Recording Infrastructure (#2020-#2022)
| Feature | Description | Status |
|---------|-------------|--------|
| #2020 | FunctionRecord struct | Completed |
| #2021 | RecordingSession management | Completed |
| #2022 | Thread-local recording storage | Completed |

### Function Tracking (#2023-#2025)
| Feature | Description | Status |
|---------|-------------|--------|
| #2023 | Function call recording | Completed |
| #2024 | Function return tracking | Completed |
| #2025 | Call graph edge tracking (callees) | Completed |

### Call Count & Timing (#2026-#2027)
| Feature | Description | Status |
|---------|-------------|--------|
| #2026 | Call count instrumentation | Completed |
| #2027 | First/last call timing (microseconds) | Completed |

### Export & Integration (#2028-#2029)
| Feature | Description | Status |
|---------|-------------|--------|
| #2028 | SDN export (export_layout_sdn) | Completed |
| #2029 | LayoutConfig export (export_layout_config) | Completed |

## Implementation Details

### New Module: layout_recorder.rs

Created `src/compiler/src/layout_recorder.rs` (~460 lines) with:

```rust
// Per-function execution record
pub struct FunctionRecord {
    pub name: String,
    pub module: Option<String>,
    pub call_count: u64,
    pub first_call_us: u64,
    pub last_call_us: u64,
    pub estimated_size: u64,
    pub callees: Vec<String>,
    pub is_startup_path: bool,
}

// Recording session data
pub struct RecordingSession {
    pub functions: HashMap<String, FunctionRecord>,
    pub call_stack: Vec<String>,
    pub start_time: Option<Instant>,
    pub first_frame_us: Option<u64>,
    pub event_loop_us: Option<u64>,
}

// Global recording API
pub fn start_recording();
pub fn stop_recording();
pub fn is_recording() -> bool;
pub fn record_function_call(name: &str);
pub fn record_function_return();
pub fn record_layout_marker(marker: &str);
pub fn export_layout_sdn() -> String;
pub fn export_layout_config() -> LayoutConfig;
```

### Phase Inference Algorithm

```rust
impl FunctionRecord {
    pub fn inferred_phase(&self, first_frame_threshold_us: u64) -> LayoutPhase {
        if self.call_count == 0 { return LayoutPhase::Cold; }

        if self.first_call_us < first_frame_threshold_us {
            if self.call_count == 1 {
                LayoutPhase::Startup        // Called once early = startup code
            } else if self.first_call_us < first_frame_threshold_us / 2 {
                LayoutPhase::FirstFrame     // Called early and multiple times
            } else {
                LayoutPhase::Steady
            }
        } else if self.call_count < 10 {
            LayoutPhase::Cold               // Called rarely after startup
        } else {
            LayoutPhase::Steady             // Called frequently after startup
        }
    }
}
```

### Interpreter Integration

Modified `src/compiler/src/interpreter_call/core.rs`:
```rust
fn exec_function_inner(...) -> Result<Value, CompileError> {
    // Layout recording for 4KB page locality optimization
    crate::layout_recorder::record_function_call(&func.name);

    // ... function execution ...

    crate::layout_recorder::record_function_return();
    Ok(result)
}
```

Modified `src/compiler/src/interpreter_extern.rs`:
```rust
"simple_layout_mark" => {
    // Record marker for layout phase boundaries
    crate::layout_recorder::record_layout_marker(&marker_name);
    Ok(Value::Nil)
}
```

### Module Registration

Updated `src/compiler/src/lib.rs`:
```rust
pub mod layout_recorder;

pub use layout_recorder::{
    start_recording, stop_recording, is_recording, record_function_call,
    record_function_return, record_layout_marker, export_layout_sdn,
    export_layout_config, clear_recording, merge_with_config,
};
```

## Files Modified

| File | Changes |
|------|---------|
| `src/compiler/src/layout_recorder.rs` | NEW - Recording infrastructure (~460 lines) |
| `src/compiler/src/lib.rs` | Added module and re-exports |
| `src/compiler/src/interpreter_call/core.rs` | Added recording calls |
| `src/compiler/src/interpreter_extern.rs` | Added marker recording |
| `src/compiler/src/interpreter.rs` | Fixed mutable reference bug |
| `src/compiler/src/linker/parallel.rs` | Fixed SmfSymbol test initializers |

## Test Coverage

The layout_recorder module includes 5 unit tests:
1. `test_function_record_phase_inference` - Validates phase inference algorithm
2. `test_recording_session` - Tests session management and call graph
3. `test_recording_markers` - Tests marker recording
4. `test_global_recording` - Tests global start/stop API
5. `test_export_sdn` - Tests SDN export format

## Usage Example

```rust
use simple_compiler::{start_recording, stop_recording, export_layout_sdn};

// Enable recording before test execution
start_recording();

// Run tests - all function calls are recorded
run_test_suite();

// Stop and export recorded data
stop_recording();
let sdn = export_layout_sdn();
std::fs::write("layout.sdn", sdn).unwrap();
```

## What Gets Recorded

- **Call counts**: How many times each function is called
- **First call timing**: When each function is first called (startup vs steady)
- **Call graph edges**: Which functions call which (for grouping)
- **Layout markers**: Phase boundary events (first_frame, event_loop.enter, etc.)

## Phase Progression

| Phase | Features | Status | Progress |
|-------|----------|--------|----------|
| Phase 1 | #2000-#2008 (9) | Complete | Language & Parser + Compiler IR |
| Phase 2 | #2010-#2019 (10) | Complete | SDN Schema + Config Loader |
| Phase 3 | #2020-#2029 (10) | Complete | Test Framework Recording |
| Phase 4 | #2030-#2039 (10) | Planned | SMF/ELF Linker Integration |
| Phase 5 | #2040-#2049 (10) | Planned | Runtime Hot Path Analysis |

## Next Steps (Phase 4)

Phase 4 will implement SMF/ELF linker integration:
- Section ordering by layout phase
- Symbol grouping for cache locality
- Profile-guided section layout
- Hot/cold code splitting

## Build Status

- Workspace build: Passed
- Warnings: 126 (pre-existing, unrelated to this phase)
- Test infrastructure: FFI linker issue (pre-existing)

## Related Reports

- Phase 1: [4KB_PAGE_LOCALITY_PHASE1_2025-12-28.md](4KB_PAGE_LOCALITY_PHASE1_2025-12-28.md)
- Phase 2: [4KB_PAGE_LOCALITY_PHASE2_2025-12-28.md](4KB_PAGE_LOCALITY_PHASE2_2025-12-28.md)
