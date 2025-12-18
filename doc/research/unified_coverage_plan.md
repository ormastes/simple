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

**Goal:** Merge Rust + Simple coverage into unified report

#### Step 1: FFI Mapping Table
```rust
// src/util/coverage_tools/src/ffi_map.rs

pub struct FfiMap {
    mappings: HashMap<String, FfiBinding>,
}

pub struct FfiBinding {
    simple_function: String,
    rust_ffi: String,
    rust_file: PathBuf,
    rust_line: usize,
}

impl FfiMap {
    pub fn from_annotations() -> Self {
        // Parse FFI annotations from Rust code
        // Example: #[ffi(simple = "Array.push")]
        // Or read from generated ffi_map.json
    }
}
```

#### Step 2: Merger Implementation
```rust
// src/util/coverage_tools/src/bin/coverage_merge.rs

fn main() -> Result<()> {
    let args = Args::parse();

    let rust_cov = RustCoverage::from_file(&args.rust)?;
    let simple_cov = SimpleCoverage::from_file(&args.simple)?;
    let ffi_map = FfiMap::from_annotations()?;

    let merger = CoverageMerger::new(rust_cov, simple_cov, ffi_map);
    let unified = merger.merge()?;

    unified.save_json(&args.output)?;
    unified.save_html(&args.output.with_extension("html"))?;

    Ok(())
}
```

### Phase 3: HTML Dashboard (Week 3)

**Goal:** Interactive coverage dashboard

#### Dashboard Features
- **Overview:** Rust vs Simple coverage percentages
- **File Browser:** Navigate Rust and Simple files
- **FFI View:** List all FFI bindings with status
- **Feature View:** Per-feature coverage breakdown
- **Gap Highlights:** Red highlights for untested paths

#### Template
```html
<!-- target/coverage/unified/index.html -->
<!DOCTYPE html>
<html>
<head>
    <title>Simple Unified Coverage</title>
    <style>
        .coverage-high { background: #c8e6c9; }
        .coverage-medium { background: #fff9c4; }
        .coverage-low { background: #ffccbc; }
        .coverage-none { background: #ffebee; }
        .ffi-both-tested { color: green; }
        .ffi-gap { color: red; font-weight: bold; }
    </style>
</head>
<body>
    <h1>Simple Unified Coverage Report</h1>

    <div class="summary">
        <div class="metric">
            <h3>Rust Coverage</h3>
            <div class="percentage">85.0%</div>
            <div>8500 / 10000 lines</div>
        </div>
        <div class="metric">
            <h3>Simple Coverage</h3>
            <div class="percentage">65.3%</div>
            <div>980 / 1500 lines</div>
        </div>
        <div class="metric">
            <h3>FFI Bindings</h3>
            <div class="percentage">80%</div>
            <div>40 / 50 tested</div>
        </div>
    </div>

    <h2>Coverage Gaps</h2>
    <ul class="gaps">
        <li class="ffi-gap">
            Array.filter - Rust tested (100%) but Simple wrapper not tested
            <a href="#simple/std_lib/test/unit/core/array_spec.spl">Add test</a>
        </li>
    </ul>

    <h2>Feature Coverage</h2>
    <table>
        <tr>
            <th>Feature</th>
            <th>Rust</th>
            <th>Simple</th>
            <th>System</th>
        </tr>
        <tr>
            <td>Collections</td>
            <td class="coverage-high">92.5%</td>
            <td class="coverage-medium">68.0%</td>
            <td>3 tests</td>
        </tr>
    </table>
</body>
</html>
```

### Phase 4: Makefile Integration (Week 3)

**Goal:** Add coverage targets to Makefile

```makefile
# Unified coverage (Rust + Simple)
coverage-unified:
	@echo "=== UNIFIED COVERAGE (Rust + Simple) ==="
	@mkdir -p $(COVERAGE_DIR)/unified

	# Run Rust tests with coverage
	LLVM_PROFILE_FILE="$(COVERAGE_DIR)/rust_%p.profraw" \
		cargo test --workspace

	# Convert to JSON
	cargo llvm-cov --no-run --json \
		--output-path=$(COVERAGE_DIR)/rust_coverage.json

	# Run Simple tests with coverage
	SIMPLE_COVERAGE=1 \
	SIMPLE_COVERAGE_OUTPUT=$(COVERAGE_DIR)/simple_coverage.json \
		cargo test -p simple-driver -- simple_stdlib

	# Merge coverage
	cargo run -p simple-coverage-tools --bin coverage-merge \
		--rust $(COVERAGE_DIR)/rust_coverage.json \
		--simple $(COVERAGE_DIR)/simple_coverage.json \
		--output $(COVERAGE_DIR)/unified/unified_coverage.json

	# Generate HTML
	cargo run -p simple-coverage-tools --bin coverage-html \
		--input $(COVERAGE_DIR)/unified/unified_coverage.json \
		--output $(COVERAGE_DIR)/unified/index.html

	@echo ""
	@echo "Unified coverage report: $(COVERAGE_DIR)/unified/index.html"
	@echo "  Rust:   $(shell jq -r '.rust.percent' $(COVERAGE_DIR)/unified/unified_coverage.json)%"
	@echo "  Simple: $(shell jq -r '.simple.percent' $(COVERAGE_DIR)/unified/unified_coverage.json)%"
	@echo "  Gaps:   $(shell jq -r '.gaps | length' $(COVERAGE_DIR)/unified/unified_coverage.json)"

# Coverage check with thresholds
coverage-check-unified:
	@make coverage-unified
	@echo ""
	@echo "=== CHECKING COVERAGE THRESHOLDS ==="
	@cargo run -p simple-coverage-tools --bin coverage-check \
		--input $(COVERAGE_DIR)/unified/unified_coverage.json \
		--rust-threshold 85 \
		--simple-threshold 80 \
		--ffi-threshold 90
```

### Phase 5: CI Integration (Week 4)

**Goal:** Run unified coverage on every PR

#### GitHub Actions Workflow
```yaml
# .github/workflows/coverage.yml
name: Coverage

on:
  pull_request:
  push:
    branches: [main]

jobs:
  unified-coverage:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Install Rust
        uses: dtolnay/rust-toolchain@stable

      - name: Install cargo-llvm-cov
        run: cargo install cargo-llvm-cov

      - name: Run unified coverage
        run: make coverage-unified

      - name: Check coverage thresholds
        run: make coverage-check-unified

      - name: Upload coverage report
        uses: actions/upload-artifact@v4
        with:
          name: coverage-report
          path: target/coverage/unified/

      - name: Comment coverage summary on PR
        uses: actions/github-script@v7
        with:
          script: |
            const fs = require('fs');
            const coverage = JSON.parse(
              fs.readFileSync('target/coverage/unified/unified_coverage.json', 'utf8')
            );

            const comment = `
            ## Coverage Report

            | Component | Coverage | Change |
            |-----------|----------|--------|
            | Rust      | ${coverage.rust.percent}% | +0.5% |
            | Simple    | ${coverage.simple.percent}% | +2.1% |
            | FFI       | ${(coverage.ffi_bindings.filter(b => b.status === 'both_tested').length / coverage.ffi_bindings.length * 100).toFixed(1)}% | +1.0% |

            ### Gaps Detected
            ${coverage.gaps.map(g => `- ${g.function}: ${g.recommendation}`).join('\n')}

            [View full report](https://github.com/${context.repo.owner}/${context.repo.repo}/actions/runs/${context.runId})
            `;

            github.rest.issues.createComment({
              issue_number: context.issue.number,
              owner: context.repo.owner,
              repo: context.repo.repo,
              body: comment
            });
```

---

## 6. Coverage Report Format

### 6.1 Dashboard Overview

```
┌─────────────────────────────────────────────────────────────┐
│              Simple Unified Coverage Report                 │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐     │
│  │ Rust         │  │ Simple       │  │ FFI Bindings │     │
│  │ 85.0%        │  │ 65.3%        │  │ 80%          │     │
│  │ 8500/10000   │  │ 980/1500     │  │ 40/50        │     │
│  └──────────────┘  └──────────────┘  └──────────────┘     │
│                                                             │
│  Coverage Trend:                                            │
│  ████████████████████░░░░░░░░░ 85% ↑ +2.3%                │
│                                                             │
├─────────────────────────────────────────────────────────────┤
│ Coverage Gaps (10)                                          │
├─────────────────────────────────────────────────────────────┤
│ ⚠️  Array.filter - Rust tested, Simple wrapper not tested  │
│ ⚠️  Dict.merge - No system tests                           │
│ ⚠️  Actor.spawn - FFI binding not verified                 │
└─────────────────────────────────────────────────────────────┘
```

### 6.2 Feature Coverage View

```
┌──────────────────────────────────────────────────────────────┐
│ Feature: Collections (#15)                                   │
├──────────────────────────────────────────────────────────────┤
│ Rust Implementation: 92.5% (185/200 lines)                   │
│   ✅ src/runtime/src/value/collections.rs                    │
│   ✅ src/compiler/src/codegen/instr_collections.rs           │
│                                                              │
│ Simple Stdlib: 68.0% (102/150 lines)                         │
│   ✅ simple/std_lib/src/core/array.spl (80%)                 │
│   ⚠️  simple/std_lib/src/core/dict.spl (55%)                 │
│                                                              │
│ System Tests: 3 tests                                        │
│   ✅ array_types_spec.spl                                    │
│   ✅ dictionary_types_spec.spl                               │
│   ❌ No integration test for Dict+Array interaction          │
│                                                              │
│ FFI Bindings: 8/10 tested                                    │
│   ✅ simple_array_push                                       │
│   ✅ simple_array_pop                                        │
│   ⚠️  simple_array_filter (Rust tested, Simple not)         │
│   ⚠️  simple_dict_merge (Neither tested)                     │
└──────────────────────────────────────────────────────────────┘
```

---

## 7. CI Integration

### 7.1 Coverage Enforcement

**PR Check Requirements:**
- ✅ Rust coverage ≥ 85%
- ✅ Simple coverage ≥ 80%
- ✅ FFI bindings ≥ 90% verified
- ✅ No new gaps introduced

**Example CI Output:**
```
Running unified coverage...

Rust Coverage:    85.2% ✅ (threshold: 85%)
Simple Coverage:  81.3% ✅ (threshold: 80%)
FFI Coverage:     88.0% ❌ (threshold: 90%)

❌ Coverage check FAILED

Gaps detected:
  - Array.filter: Rust tested (100%), Simple wrapper not tested
  - Actor.send: FFI binding not verified

Recommendations:
  1. Add test to simple/std_lib/test/unit/core/array_spec.spl for Array.filter
  2. Add system test for Actor.send in simple/test/system/features/actors/

View full report: https://github.com/.../actions/runs/12345
```

### 7.2 Coverage Diff

**Show coverage changes in PR:**
```
Coverage Changes:

src/runtime/src/value/collections.rs
  Lines:    185/200 → 192/200 (+7)
  Branches: 48/60 → 52/60 (+4)
  Coverage: 92.5% → 96.0% (+3.5%) ✅

simple/std_lib/src/core/array.spl
  Lines:    102/150 → 120/150 (+18)
  Coverage: 68.0% → 80.0% (+12.0%) ✅

FFI Bindings:
  + simple_array_filter now tested ✅
  - simple_dict_merge still untested ⚠️
```

---

## 8. Feature Tracking

### 8.1 Per-Feature Coverage Matrix

**Track coverage at all levels for each feature:**

| Feature | Rust | Simple | System | FFI | Status |
|---------|------|--------|--------|-----|--------|
| **Collections (#15)** | 92% | 68% | 3 tests | 80% | ⚠️ Gaps |
| **Actors (#27)** | 88% | 75% | 2 tests | 100% | ✅ Complete |
| **Async (#28)** | 95% | 60% | 1 test | 75% | ⚠️ Gaps |
| **Generators (#29)** | 90% | 0% | 0 tests | 0% | ❌ Not Tested |

### 8.2 Feature Coverage Report

**Generate per-feature report:**
```bash
cargo run -p simple-coverage-tools --bin feature-coverage \
    --input target/coverage/unified/unified_coverage.json \
    --output target/coverage/feature_coverage.md
```

**Output (feature_coverage.md):**
```markdown
# Feature Coverage Report

## Collections (#15) - ⚠️ Gaps Detected

**Overall:** 82.5% covered

### Rust Implementation
- **Coverage:** 92.5% (185/200 lines)
- **Files:**
  - src/runtime/src/value/collections.rs (95%)
  - src/compiler/src/codegen/instr_collections.rs (90%)

### Simple Stdlib
- **Coverage:** 68.0% (102/150 lines)
- **Files:**
  - simple/std_lib/src/core/array.spl (80%)
  - simple/std_lib/src/core/dict.spl (55%)

### System Tests
- **Count:** 3 tests
- **Files:**
  - array_types_spec.spl ✅
  - dictionary_types_spec.spl ✅

### FFI Bindings
- **Verified:** 8/10 (80%)
- **Gaps:**
  - simple_array_filter - Rust tested, Simple not
  - simple_dict_merge - Neither tested

### Recommendations
1. Add tests for Dict methods (merge, filter)
2. Add system test for Array+Dict interaction
3. Verify simple_array_filter FFI binding
```

---

## 9. Appendix A: New Feature IDs

| ID | Feature | Impact | Effort | Priority |
|----|---------|--------|--------|----------|
| **#674** | Simple Coverage Instrumentation | Enable Simple test coverage | 1 week | 🔥 High |
| **#675** | Coverage Merger Tool | Unified Rust+Simple reports | 1 week | 🔥 High |
| **#676** | FFI Mapping Generator | Auto-generate FFI mapping table | 3 days | 🟡 Medium |
| **#677** | Unified Coverage Dashboard | Interactive HTML report | 1 week | 🟡 Medium |
| **#678** | CI Coverage Checks | Automated PR coverage checks | 2 days | 🔥 High |
| **#679** | Feature Coverage Tracker | Per-feature coverage matrix | 3 days | 🟢 Low |

**Total:** 6 features, estimated **4 weeks** (1 engineer)

**Quick Win (2 weeks):**
1. #674 Simple Coverage Instrumentation (1 week)
2. #675 Coverage Merger Tool (1 week)
3. Basic HTML report (no fancy dashboard)

---

## 10. Appendix B: Migration Path

### Current State → Unified Coverage

**Week 1: No Breaking Changes**
```bash
# Old commands still work
make coverage-unit        # Rust only
make coverage-merged      # Rust only

# New command available
make coverage-unified     # Rust + Simple
```

**Week 2: Gradual Adoption**
```bash
# Optional: Enable Simple coverage for specific tests
SIMPLE_COVERAGE=1 cargo test simple_stdlib
```

**Week 3: CI Integration**
```bash
# CI runs unified coverage (non-blocking warnings)
make coverage-unified
make coverage-check-unified || echo "Coverage gaps detected (warning)"
```

**Week 4: Enforcement**
```bash
# CI fails on coverage gaps
make coverage-check-unified  # Exit 1 if thresholds not met
```

---

## Conclusion

Unified coverage reporting bridges the gap between Rust compiler tests and Simple stdlib tests, providing **complete visibility** into end-to-end test coverage.

**Key Benefits:**
- ✅ **100% Visibility** - See exactly what's tested at all levels
- ✅ **Automated Gap Detection** - Catch untested FFI paths automatically
- ✅ **Feature Tracking** - Per-feature coverage dashboards
- ✅ **CI Integration** - Automated coverage checks on every PR

**Implementation:** 4 weeks, 6 new features, backwards-compatible rollout

**Next Steps:**
1. Review and approve this plan
2. Implement Phase 1 (Simple coverage instrumentation)
3. Build coverage merger tool
4. Deploy unified dashboard
5. Integrate with CI

---

**END OF DOCUMENT**
