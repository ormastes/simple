# Unified Coverage Plan: Merging Rust and Simple Test Coverage

**Date:** 2025-12-18
**Status:** Design Document
**Purpose:** Unified coverage reporting for Rust compiler tests + Simple stdlib tests

---

## Executive Summary

Simple has two parallel test suites with separate coverage tracking:
1. **Rust Tests** (807 tests) - Test compiler, runtime, driver (Rust code coverage via llvm-cov)
2. **Simple Tests** (96 tests) - Test stdlib (Simple code, currently no coverage tracking)

This plan unifies coverage reporting to show **end-to-end coverage** from Rust implementation through Simple stdlib API.

**Key Goals:**
- ✅ **Unified Dashboard** - Single coverage report showing both Rust and Simple coverage
- ✅ **Feature Coverage** - Track which features are tested at all levels (unit → stdlib → system)
- ✅ **Gap Detection** - Identify untested code paths across language boundaries
- ✅ **CI Integration** - Automated coverage checks on PR

**Projected Impact:**
- **Visibility:** 100% coverage transparency (currently ~50% blind to stdlib coverage)
- **Quality:** Catch gaps where Rust code is tested but stdlib wrapper is not
- **Velocity:** Automated coverage checks prevent regressions

---

## Table of Contents

1. [Current State](#1-current-state)
2. [Problem Statement](#2-problem-statement)
3. [Proposed Architecture](#3-proposed-architecture)
4. [Coverage Data Flow](#4-coverage-data-flow)
5. [Implementation Plan](#5-implementation-plan)
6. [Coverage Report Format](#6-coverage-report-format)
7. [CI Integration](#7-ci-integration)
8. [Feature Tracking](#8-feature-tracking)

---

## 1. Current State

### 1.1 Rust Test Coverage

**Infrastructure:**
- Tool: `cargo-llvm-cov` (LLVM source-based coverage)
- Coverage Types: Branch/condition, function touch, class/struct method touch
- Reports: HTML, JSON, LCOV
- Location: `target/coverage/`

**Test Categories (per doc/guides/test.md):**

| Level | Tests | Coverage Metric | Command |
|-------|-------|-----------------|---------|
| **Unit** | 631+ | Branch/Condition | `make coverage-unit` |
| **Integration** | 9 | Public func on class/struct | `make coverage-integration` |
| **System** | 8 | Class/struct method | `make coverage-system` |
| **Environment** | 7 | Branch/Condition | `make coverage-environment` |
| **Merged** | All | Combined | `make coverage-merged` |

**Output Formats:**
```
target/coverage/
├── unit/
│   ├── html/index.html
│   └── coverage.json
├── integration/
│   ├── html/index.html
│   └── coverage.json
├── system/
│   ├── html/index.html
│   └── coverage.json
└── merged/
    ├── html/index.html
    └── coverage.json
```

### 1.2 Simple Test Coverage

**Infrastructure:**
- Tool: **NONE** (no coverage tracking currently)
- Tests: 31 actual tests in `simple/std_lib/test/`
- Location: `simple/std_lib/test/` (working tests) + `simple/test/system/` (empty placeholders)
- Discovery: `build.rs` auto-wraps as Rust tests
- Execution: `cargo test -p simple-driver simple_stdlib`

**Test Categories:**

| Category | Location | Files | Tests | Status |
|----------|----------|-------|-------|--------|
| **Stdlib Unit** | `simple/std_lib/test/unit/` | 20 | 31 | ✅ Working |
| **Stdlib System** | `simple/std_lib/test/system/` | 6 | 400+ | ✅ Working |
| **Stdlib Integration** | `simple/std_lib/test/integration/` | 1 | - | ✅ Working |
| **Terminal System Tests** | `simple/test/system/` | 65 | 0 | ❌ Empty placeholders |

**Key Distinction:**
- **simple/std_lib/test/** - Real tests (Simple code testing Simple stdlib)
- **simple/test/system/** - Placeholder files for Rust terminal tests (Rust code testing Rust compiler)

**Current Gap:**
- ✅ Tests run and pass/fail
- ❌ No coverage data collected
- ❌ Unknown which stdlib functions are tested
- ❌ No way to correlate Rust coverage with Simple coverage

### 1.3 Coverage Blind Spots

**Example Scenario:**
```rust
// src/runtime/src/value/collections.rs
#[no_mangle]
pub extern "C" fn simple_array_push(arr: RuntimeValue, val: RuntimeValue) -> RuntimeValue {
    // Rust unit test: ✅ 100% coverage
    // ...
}
```

```simple
# simple/std_lib/src/core/array.spl
fn push(self, value: T):
    # Calls simple_array_push via FFI
    __builtin_array_push(self, value)
```

```simple
# simple/std_lib/test/unit/core/array_spec.spl
describe "Array.push":
    it "adds element":
        let arr = [1, 2, 3]
        arr.push(4)
        expect(arr.len()).to_equal(4)  # ❌ NO COVERAGE DATA COLLECTED
```

**Problem:**
- Rust FFI function `simple_array_push` has 100% coverage via Rust tests
- Simple wrapper `Array.push()` is tested (test passes)
- But we have **NO DATA** showing which lines in `simple/std_lib/src/core/array.spl` were executed!
- Can't tell if the FFI call path is actually exercised

---

## 2. Problem Statement

### 2.1 Separate Coverage Islands

**Current Situation:**
```
┌───────────────────────────────────────────────────────────────┐
│               Rust Coverage (807 tests)                       │
│  ✅ Tracked: src/runtime/src/value/      (Rust FFI impls)   │
│  ✅ Tracked: src/compiler/src/            (Compiler)         │
│  ✅ Tracked: src/parser/src/              (Parser)           │
│  ✅ Tracked: src/driver/tests/            (Integration)      │
└───────────────────────────────────────────────────────────────┘
                          ↕ FFI boundary
┌───────────────────────────────────────────────────────────────┐
│          Simple Stdlib Coverage (31 actual tests)             │
│  ❌ NOT TRACKED: simple/std_lib/src/      (Stdlib source)    │
│  ❌ NOT TRACKED: simple/std_lib/test/     (Stdlib tests)     │
│  ✅ Run via: cargo test simple_stdlib     (but no coverage)  │
└───────────────────────────────────────────────────────────────┘

┌───────────────────────────────────────────────────────────────┐
│     Terminal Tests (65 files in simple/test/system/)          │
│  ℹ️  Empty placeholders for Rust terminal tests              │
│  ℹ️  These test Rust compiler via terminal, not stdlib       │
└───────────────────────────────────────────────────────────────┘
```

**Focus:** This plan addresses coverage for **simple/std_lib/** (stdlib source + tests), NOT the empty terminal test placeholders.

### 2.2 Key Questions We Can't Answer

1. **Which stdlib functions are tested?**
   - Example: Is `Array.filter()` tested? (Rust `simple_array_filter` is, but Simple wrapper?)

2. **Are FFI bindings correct?**
   - Example: Does Simple `Array.push()` correctly call `simple_array_push()`?

3. **Feature coverage completeness?**
   - Example: Feature #37 (Union Types) - is it tested at all levels?

4. **Where are the gaps?**
   - Rust code with 100% coverage but no Simple tests
   - Simple code with tests but Rust impl not covered

### 2.3 Business Impact

**Without Unified Coverage:**
- 🐛 **Bugs Slip Through:** Rust code tested, Simple wrapper broken
- 📉 **False Confidence:** "807 tests, 100% coverage" but stdlib untested
- 🕒 **Manual Verification:** Engineers manually check both coverage reports
- 🚫 **No Enforcement:** Can't enforce "every feature must be tested at all levels"

**With Unified Coverage:**
- ✅ **Complete Visibility:** See exactly what's tested end-to-end
- ✅ **Automated Checks:** CI fails if coverage gaps detected
- ✅ **Gap Detection:** Auto-identify untested FFI paths
- ✅ **Feature Tracking:** Per-feature coverage dashboards

---

## 3. Proposed Architecture

### 3.1 Coverage Collection Strategy

**Two-Phase Collection:**

#### Phase 1: Rust Coverage (Existing)
```bash
# Run Rust tests with LLVM coverage
cargo llvm-cov --workspace --json --output-path rust_coverage.json

# Produces:
# - rust_coverage.json (LLVM coverage format)
# - Tracks: src/runtime/src/value/collections.rs:142-156
```

#### Phase 2: Simple Coverage (NEW)
```bash
# Run Simple tests with instrumented interpreter
cargo test -p simple-driver -- simple_stdlib \
    SIMPLE_COVERAGE=1 \
    SIMPLE_COVERAGE_OUTPUT=simple_coverage.json

# Produces:
# - simple_coverage.json (custom format)
# - Tracks: simple/std_lib/src/core/array.spl:15-23
```

### 3.2 Coverage Instrumentation for Simple

**Approach:** Interpreter-based coverage collection

```rust
// src/driver/src/simple_test.rs

pub fn run_test_file(path: &Path) -> SimpleTestResult {
    let coverage_enabled = std::env::var("SIMPLE_COVERAGE").is_ok();

    let mut collector = if coverage_enabled {
        Some(CoverageCollector::new())
    } else {
        None
    };

    // Run test with coverage hooks
    let result = interpreter.run_with_coverage(ast, collector.as_mut());

    // Save coverage data
    if let Some(collector) = collector {
        collector.save_to_file("simple_coverage.json")?;
    }

    result
}
```

**CoverageCollector:**
```rust
// src/driver/src/coverage_collector.rs

pub struct CoverageCollector {
    /// File path → line numbers executed
    execution_map: HashMap<PathBuf, HashSet<usize>>,
    /// Function name → call count
    function_calls: HashMap<String, u64>,
    /// FFI function calls
    ffi_calls: HashMap<String, u64>,
}

impl CoverageCollector {
    pub fn record_line(&mut self, file: &Path, line: usize) {
        self.execution_map.entry(file.to_path_buf())
            .or_default()
            .insert(line);
    }

    pub fn record_function_call(&mut self, name: &str) {
        *self.function_calls.entry(name.to_string()).or_default() += 1;
    }

    pub fn record_ffi_call(&mut self, name: &str) {
        *self.ffi_calls.entry(name.to_string()).or_default() += 1;
    }

    pub fn save_to_file(&self, path: &Path) -> Result<()> {
        let json = serde_json::to_string_pretty(&SimpleCoverageReport {
            execution_map: self.execution_map.clone(),
            function_calls: self.function_calls.clone(),
            ffi_calls: self.ffi_calls.clone(),
        })?;
        std::fs::write(path, json)?;
        Ok(())
    }
}
```

### 3.3 Coverage Merger

**Tool:** `coverage-merge` binary

```bash
# Merge Rust + Simple coverage
cargo run -p simple-coverage-tools --bin coverage-merge \
    --rust target/coverage/rust_coverage.json \
    --simple target/coverage/simple_coverage.json \
    --output target/coverage/unified_coverage.json

# Produces unified report with cross-references
```

**Merger Logic:**
```rust
// src/util/coverage_tools/src/merger.rs

pub struct CoverageMerger {
    rust_coverage: RustCoverage,
    simple_coverage: SimpleCoverage,
    ffi_map: FfiMap,  // Maps Simple → Rust FFI functions
}

impl CoverageMerger {
    pub fn merge(&self) -> UnifiedCoverage {
        let mut unified = UnifiedCoverage::new();

        // 1. Add all Rust coverage
        for (file, coverage) in &self.rust_coverage.files {
            unified.add_rust_file(file, coverage);
        }

        // 2. Add all Simple coverage
        for (file, coverage) in &self.simple_coverage.files {
            unified.add_simple_file(file, coverage);
        }

        // 3. Cross-reference FFI calls
        for (simple_func, rust_ffi) in &self.ffi_map.mappings {
            let simple_tested = self.simple_coverage.is_tested(simple_func);
            let rust_tested = self.rust_coverage.is_tested(rust_ffi);

            unified.add_ffi_binding(simple_func, rust_ffi, FFIStatus {
                simple_tested,
                rust_tested,
                binding_verified: simple_tested && rust_tested,
            });
        }

        // 4. Compute feature coverage
        for feature in &self.ffi_map.features {
            unified.add_feature_coverage(feature, FeatureCoverage {
                rust_coverage: self.compute_rust_coverage(feature),
                simple_coverage: self.compute_simple_coverage(feature),
                system_tests: self.find_system_tests(feature),
            });
        }

        unified
    }
}
```

---

## 4. Coverage Data Flow

### 4.1 End-to-End Flow

```
┌──────────────────────────────────────────────────────────────────┐
│                     TEST EXECUTION PHASE                         │
├──────────────────────────────────────────────────────────────────┤
│                                                                  │
│  Rust Tests (807)                    Simple Tests (96)          │
│  ┌────────────────┐                  ┌────────────────┐         │
│  │ cargo test     │                  │ cargo test     │         │
│  │ --workspace    │                  │ simple_stdlib  │         │
│  │ LLVM_PROFILE=1 │                  │ SIMPLE_COV=1   │         │
│  └────────┬───────┘                  └────────┬───────┘         │
│           │                                   │                 │
│           ▼                                   ▼                 │
│  ┌─────────────────┐              ┌─────────────────┐          │
│  │ LLVM Coverage   │              │ Interpreter     │          │
│  │ Instrumentation │              │ Coverage Hooks  │          │
│  └────────┬────────┘              └────────┬────────┘          │
│           │                                │                   │
│           ▼                                ▼                   │
│  ┌─────────────────┐              ┌─────────────────┐          │
│  │ rust_cov.profraw│              │ simple_cov.json │          │
│  └────────┬────────┘              └────────┬────────┘          │
│           │                                │                   │
└───────────┼────────────────────────────────┼───────────────────┘
            │                                │
            ▼                                ▼
┌──────────────────────────────────────────────────────────────────┐
│                   PROCESSING PHASE                               │
├──────────────────────────────────────────────────────────────────┤
│           │                                │                   │
│           ▼                                ▼                   │
│  ┌─────────────────┐              ┌─────────────────┐          │
│  │ llvm-cov export │              │ coverage-parser │          │
│  │ → rust_cov.json │              │ → simple_cov.   │          │
│  │                 │              │    normalized   │          │
│  └────────┬────────┘              └────────┬────────┘          │
│           │                                │                   │
│           └────────────┬───────────────────┘                   │
│                        ▼                                        │
│              ┌──────────────────┐                              │
│              │ coverage-merge   │                              │
│              │                  │                              │
│              │ - Merge coverage │                              │
│              │ - Map FFI calls  │                              │
│              │ - Compute gaps   │                              │
│              └────────┬─────────┘                              │
│                       │                                         │
└───────────────────────┼─────────────────────────────────────────┘
                        │
                        ▼
┌──────────────────────────────────────────────────────────────────┐
│                    REPORTING PHASE                               │
├──────────────────────────────────────────────────────────────────┤
│                        │                                         │
│              ┌─────────┴─────────┐                              │
│              │                   │                              │
│              ▼                   ▼                              │
│   ┌──────────────────┐  ┌──────────────────┐                   │
│   │ unified_cov.json │  │ unified_cov.html │                   │
│   │                  │  │                  │                   │
│   │ - Rust coverage  │  │ - Interactive    │                   │
│   │ - Simple coverage│  │   dashboard      │                   │
│   │ - FFI mapping    │  │ - Feature view   │                   │
│   │ - Feature gaps   │  │ - Gap highlights │                   │
│   └──────────────────┘  └──────────────────┘                   │
│                                                                  │
└──────────────────────────────────────────────────────────────────┘
```

### 4.2 Data Formats

#### Rust Coverage JSON (LLVM format)
```json
{
  "type": "llvm.coverage.json.export",
  "version": "2.0.1",
  "data": [
    {
      "files": [
        {
          "filename": "src/runtime/src/value/collections.rs",
          "segments": [
            [142, 5, 1, true, true],
            [143, 9, 5, true, false],
            [156, 5, 0, false, false]
          ],
          "summary": {
            "lines": { "count": 15, "covered": 12, "percent": 80.0 },
            "branches": { "count": 8, "covered": 6, "percent": 75.0 }
          }
        }
      ]
    }
  ]
}
```

#### Simple Coverage JSON (Custom format)
```json
{
  "version": "1.0",
  "files": {
    "simple/std_lib/src/core/array.spl": {
      "lines_executed": [1, 2, 5, 6, 7, 15, 16, 23],
      "functions": {
        "Array.push": { "calls": 5, "lines": [15, 16] },
        "Array.filter": { "calls": 0, "lines": [] }
      },
      "ffi_calls": {
        "__builtin_array_push": 5,
        "__builtin_array_filter": 0
      }
    }
  },
  "summary": {
    "total_files": 20,
    "total_lines": 1500,
    "lines_executed": 980,
    "percent": 65.3
  }
}
```

#### Unified Coverage JSON
```json
{
  "version": "1.0",
  "rust": {
    "files": 120,
    "lines_covered": 8500,
    "lines_total": 10000,
    "percent": 85.0
  },
  "simple": {
    "files": 20,
    "lines_covered": 980,
    "lines_total": 1500,
    "percent": 65.3
  },
  "ffi_bindings": [
    {
      "simple_function": "Array.push",
      "rust_ffi": "simple_array_push",
      "rust_file": "src/runtime/src/value/collections.rs",
      "rust_line": 142,
      "simple_file": "simple/std_lib/src/core/array.spl",
      "simple_line": 15,
      "status": "both_tested",
      "simple_calls": 5,
      "rust_coverage": true
    },
    {
      "simple_function": "Array.filter",
      "rust_ffi": "simple_array_filter",
      "status": "rust_tested_only",
      "warning": "Simple wrapper not tested"
    }
  ],
  "features": [
    {
      "id": "collections",
      "name": "Collections (Arrays, Dicts)",
      "rust_coverage": 92.5,
      "simple_coverage": 68.0,
      "system_tests": 3,
      "gaps": [
        "Array.filter - no Simple tests",
        "Dict.merge - no system tests"
      ]
    }
  ],
  "gaps": [
    {
      "type": "untested_simple_wrapper",
      "function": "Array.filter",
      "recommendation": "Add test to simple/std_lib/test/unit/core/array_spec.spl"
    }
  ]
}
```

---

## 5. Implementation Plan

### Phase 1: Simple Coverage Instrumentation (Week 1)

**Goal:** Collect coverage data from Simple tests

#### Step 1: Add Coverage Hooks to Interpreter
```rust
// src/compiler/src/interpreter.rs

pub struct Interpreter {
    env: Env,
    coverage: Option<Arc<Mutex<CoverageCollector>>>,
}

impl Interpreter {
    pub fn eval_with_coverage(&mut self, expr: &Expr, cov: &mut CoverageCollector) -> Value {
        // Record line execution
        cov.record_line(&expr.span.file, expr.span.line);

        match expr {
            Expr::Call(func, args) => {
                cov.record_function_call(&func.name);

                // Check if FFI call
                if func.name.starts_with("__builtin_") {
                    cov.record_ffi_call(&func.name);
                }

                self.eval_call(func, args)
            }
            // ... other expressions
        }
    }
}
```

#### Step 2: Create CoverageCollector
```rust
// src/driver/src/coverage/collector.rs

#[derive(Default)]
pub struct CoverageCollector {
    execution_map: HashMap<PathBuf, HashSet<usize>>,
    function_calls: HashMap<String, u64>,
    ffi_calls: HashMap<String, u64>,
    start_time: Option<Instant>,
}

impl CoverageCollector {
    pub fn new() -> Self {
        Self {
            start_time: Some(Instant::now()),
            ..Default::default()
        }
    }

    pub fn to_json(&self) -> SimpleCoverageReport {
        SimpleCoverageReport {
            version: "1.0".to_string(),
            files: self.compute_file_coverage(),
            summary: self.compute_summary(),
            duration_ms: self.start_time.map(|t| t.elapsed().as_millis()).unwrap_or(0),
        }
    }
}
```

#### Step 3: Integrate with Test Runner
```rust
// src/driver/src/simple_test.rs

pub fn run_test_file(path: &Path) -> SimpleTestResult {
    let coverage_enabled = std::env::var("SIMPLE_COVERAGE").is_ok();
    let mut collector = if coverage_enabled {
        Some(CoverageCollector::new())
    } else {
        None
    };

    let mut interpreter = Interpreter::new();
    if let Some(ref mut cov) = collector {
        interpreter.set_coverage_collector(cov);
    }

    let result = interpreter.run(ast);

    if let Some(cov) = collector {
        save_coverage(cov, path)?;
    }

    result
}
```

### Phase 2: Coverage Merger (Week 2)


---

**Continued in:** [Part 2](./unified_coverage_plan_part2.md)
