# Testing Infrastructure Roadmap 2026
## Strategic Development Plan

**Created**: 2026-01-21
**Status**: Draft
**Purpose**: Phased implementation plan for testing infrastructure gaps

---

## Executive Summary

This roadmap addresses 11 testing infrastructure components identified in the priority matrix. Based on codebase exploration, **3 components already exist** and need documentation/refinement, while **8 require new implementation**. The plan is organized into 4 phases over an estimated timeline, prioritizing high-impact, low-effort items first.

---

## Current State Assessment

### ✅ **Already Implemented** (Needs Documentation/Polish)
1. **Property-based testing** - `spec.property` module exists with QuickCheck-style generators
2. **Snapshot testing** - `spec.snapshot` module exists with multi-format support
3. **Arch compliance** - `spec.arch` module exists with dependency validation

### ❌ **Missing** (Requires Implementation)
1. **Mock lib for Simple** - No mocking framework for `.spl` files
2. **Mock prevention for Simple** - No runtime policy enforcement for Simple tests
3. **Deployment verification** - No deployment/smoke testing infrastructure
4. **Coverage for Simple source** - LLVM coverage only tracks Rust, not `.spl` files
5. **Contract testing** - No contract/interface verification
6. **Benchmarking** - No performance benchmarking framework
7. **Mutation testing** - No mutation testing for code quality validation

### ⚠️ **Partially Exists** (Needs Enhancement)
1. **Test reporting/dashboard** - Basic coverage reports exist, needs aggregation/visualization
2. **Fuzzing** - Unknown status, needs investigation

---

## Phase 1: Quick Wins (High Impact, Low Effort)
**Duration**: 1-2 weeks
**Goal**: Address critical gaps with minimal implementation complexity

### 1.1 Mock Prevention for Simple (.spl) ✅ Priority: 🔴 High
**Current State**: `simple_mock_helper` enforces mock policies in Rust tests only
**Gap**: No enforcement for Simple language tests (`.spl` files)

**Implementation Strategy**:
```simple
# New module: simple/std_lib/src/spec/mock_policy.spl
module spec.mock_policy:

    # Policy levels matching Rust test tiers
    enum TestLevel:
        Unit        # All mocks allowed
        Integration # HAL-only mocks
        System      # No mocks
        Environment # HAL + external lib mocks

    # Global policy (singleton pattern)
    static var current_policy: MockPolicy = MockPolicy.new()

    # Initialize policy (called by test runner)
    fn init_policy(level: TestLevel, patterns: [String]):
        current_policy.set_level(level)
        current_policy.set_allowed_patterns(patterns)

    # Validate mock usage at runtime
    fn check_mock_allowed(module_path: String):
        if !current_policy.is_allowed(module_path):
            panic "Mock not allowed: {module_path} (Policy: {current_policy.level})"

    # Predefined policies
    fn init_for_unit():
        init_policy(TestLevel.Unit, ["*"])  # All mocks

    fn init_for_integration():
        init_policy(TestLevel.Integration, ["hal.*", "sub_hal.*"])

    fn init_for_system():
        init_policy(TestLevel.System, [])  # No mocks
```

**Integration Points**:
1. Modify `spec.runner` to call `init_policy()` based on test directory
2. Add `@mock` decorator to track mocked functions/classes
3. Update test CLI to pass `--test-level` flag

**Effort**: Low (2-3 days)
**Files**:
- `simple/std_lib/src/spec/mock_policy.spl` (new)
- `simple/std_lib/src/spec/runner.spl` (modify)
- `simple/std_lib/test/unit/spec/mock_policy_spec.spl` (tests)

---

### 1.2 Deployment Verification Infrastructure ✅ Priority: 🔴 High
**Current State**: No smoke testing or deployment validation
**Gap**: Can't verify deployments work after release

**Implementation Strategy**:
```simple
# New module: simple/std_lib/src/spec/deployment.spl
module spec.deployment:

    # Deployment environment types
    enum Environment:
        Development
        Staging
        Production

    # Smoke test suite for deployments
    class DeploymentSuite:
        val env: Environment
        val checks: [HealthCheck]

        fn run() -> DeploymentReport:
            val results = checks.map(\check: check.execute(env))
            DeploymentReport.new(env, results)

    # Health check interface
    interface HealthCheck:
        fn execute(env: Environment) -> CheckResult
        fn name() -> String
        fn timeout() -> Duration

    # Common checks
    class ServiceHealthCheck(url: String):
        impl HealthCheck:
            fn execute(env):
                val response = http.get(url, timeout: timeout())
                if response.status == 200:
                    CheckResult.pass()
                else:
                    CheckResult.fail("HTTP {response.status}")

    class DatabaseConnectivityCheck(conn_string: String):
        impl HealthCheck:
            fn execute(env):
                try:
                    val db = Database.connect(conn_string)
                    db.ping()
                    CheckResult.pass()
                catch e:
                    CheckResult.fail("DB error: {e}")

    class APIContractCheck(api_url: String, schema: Schema):
        impl HealthCheck:
            fn execute(env):
                val response = http.get(api_url)
                if schema.validate(response.body):
                    CheckResult.pass()
                else:
                    CheckResult.fail("Schema mismatch")
```

**Deployment Test Example**:
```simple
# simple/std_lib/test/deployment/smoke_spec.spl
import spec.deployment.*

describe "Production Deployment":
    context "Critical Services":
        it "responds to health check":
            val suite = DeploymentSuite.new(
                Environment.Production,
                [
                    ServiceHealthCheck.new("https://api.simple-lang.org/health"),
                    DatabaseConnectivityCheck.new(env_var("DB_URL")),
                    APIContractCheck.new("https://api.simple-lang.org/v1", api_v1_schema)
                ]
            )
            val report = suite.run()
            expect(report.all_passed()).to(be_true)
```

**Effort**: Low (3-4 days)
**Files**:
- `simple/std_lib/src/spec/deployment.spl` (new)
- `simple/std_lib/test/deployment/` (test suite)
- `.github/workflows/deployment-verify.yml` (CI integration)

---

### 1.3 Contract Testing Foundation ✅ Priority: 🟡 Medium
**Current State**: No contract verification between modules
**Gap**: Breaking changes in APIs not caught until runtime

**Implementation Strategy**:
```simple
# New module: simple/std_lib/src/spec/contract.spl
module spec.contract:

    # Contract definition (consumer expectations)
    class Contract:
        val name: String
        val provider: String
        val consumer: String
        val interactions: [Interaction]

        fn verify() -> ContractResult:
            interactions.map(\i: i.verify()).aggregate()

    # Single interaction (request/response pair)
    class Interaction:
        val description: String
        val request: Request
        val expected_response: Response

        fn verify() -> InteractionResult:
            val actual = send_request(request)
            if expected_response.matches(actual):
                InteractionResult.pass(description)
            else:
                InteractionResult.fail(description, actual, expected_response)

    # Pact-style contract testing
    class PactBuilder:
        fn given(state: String) -> PactBuilder
        fn upon_receiving(desc: String) -> PactBuilder
        fn with_request(method: String, path: String, body: Any) -> PactBuilder
        fn will_respond_with(status: Int, body: Any) -> PactBuilder
        fn build() -> Contract
```

**Example Usage**:
```simple
# simple/std_lib/test/contract/user_service_spec.spl
describe "User Service Contract":
    it "provides user by ID":
        val contract = PactBuilder.new()
            .given("user 123 exists")
            .upon_receiving("request for user 123")
            .with_request("GET", "/users/123", nil)
            .will_respond_with(200, {id: 123, name: "Alice"})
            .build()

        expect(contract.verify()).to(be_successful)
```

**Effort**: Low (3-4 days)
**Files**:
- `simple/std_lib/src/spec/contract.spl` (new)
- `simple/std_lib/test/contract/` (test suite)

---

## Phase 2: High-Impact Foundations (High Impact, Medium Effort)
**Duration**: 3-4 weeks
**Goal**: Build core infrastructure for mocking and coverage

### 2.1 Mock Library for Simple ✅ Priority: 🔴 High
**Current State**: `simple_mock_helper` is Rust-only, no `.spl` mocking
**Gap**: Can't write isolated unit tests in Simple language

**Implementation Strategy**:

#### Option A: Reflection-Based Mocking (Recommended)
```simple
# New module: simple/std_lib/src/spec/mock.spl
module spec.mock:

    # Mock object with method stubs
    class Mock<T>:
        val _name: String
        val _stubs: Map<String, Stub>
        val _calls: [Call]

        # Create mock for interface/trait
        static fn of(name: String) -> Mock<T>:
            Mock<T>.new(name, {}, [])

        # Stub method behavior
        fn when(method: String) -> StubBuilder:
            StubBuilder.new(self, method)

        # Verify method calls
        fn verify(method: String) -> VerifyBuilder:
            VerifyBuilder.new(self, method)

        # Invoke method (called via reflection)
        fn __invoke__(method: String, args: [Any]) -> Any:
            val stub = _stubs.get(method)
            if stub.is_some():
                _calls.push(Call.new(method, args))
                stub.unwrap().invoke(args)
            else:
                panic "Unstubbed method: {method}"

    # Stub builder (fluent API)
    class StubBuilder:
        fn with_args(args: [Any]) -> StubBuilder
        fn returns(value: Any) -> Mock
        fn throws(error: Error) -> Mock
        fn calls(callback: fn([Any]) -> Any) -> Mock

    # Verification builder
    class VerifyBuilder:
        fn called() -> VerifyBuilder
        fn called_once() -> VerifyBuilder
        fn called_times(n: Int) -> VerifyBuilder
        fn with_args(args: [Any]) -> VerifyBuilder
        fn never_called() -> VerifyBuilder
```

**Example Usage**:
```simple
# simple/std_lib/test/unit/user_service_spec.spl
import spec.mock.*

describe "UserService":
    context "when creating user":
        it "saves to database":
            val db_mock = Mock.of<Database>("Database")
            db_mock.when("save")
                .with_args([User.new("Alice")])
                .returns(123)

            val service = UserService.new(db_mock)
            val user_id = service.create_user("Alice")

            expect(user_id).to(eq(123))
            db_mock.verify("save").called_once().with_args([User.new("Alice")])
```

#### Option B: Macro-Based Mocking
```simple
# Generate mock class at compile time
@mock_for(Database)
class MockDatabase:
    # Auto-generated stubs for all Database methods
    # Compiler generates: when(), verify(), etc.

# Usage
val db = MockDatabase.new()
db.when("save").returns(123)
```

**Recommendation**: Start with **Option A** (reflection-based) for flexibility, migrate to **Option B** (macro-based) later for performance.

**Effort**: Medium (1 week)
**Dependencies**: Requires reflection API in Simple runtime
**Files**:
- `simple/std_lib/src/spec/mock.spl` (core library)
- `simple/std_lib/src/spec/spy.spl` (call recording)
- `simple/std_lib/src/spec/stub.spl` (behavior stubbing)
- `simple/std_lib/test/unit/spec/mock_spec.spl` (tests)
- `doc/guide/mocking_in_simple.md` (user guide)

---

### 2.2 Coverage for Simple Source Files ✅ Priority: 🔴 High
**Current State**: `cargo llvm-cov` only tracks Rust code
**Gap**: No coverage metrics for `.spl` files

**Implementation Strategy**:

#### Step 1: Instrumentation at MIR Level
```rust
// src/compiler/coverage.rs (new)
pub struct CoverageInstrumenter {
    /// Maps (file, line) -> probe_id
    probe_map: HashMap<(PathBuf, usize), ProbeId>,
    /// Counter for unique probe IDs
    next_probe_id: usize,
}

impl CoverageInstrumenter {
    /// Insert coverage probes into MIR
    pub fn instrument_mir(&mut self, mir: &mut Mir) -> CoverageMap {
        for block in mir.blocks.iter_mut() {
            // Insert probe at block entry
            let probe_id = self.next_probe_id();
            let probe_instr = MirInstruction::CoverageProbe(probe_id);
            block.instructions.insert(0, probe_instr);

            // Map probe to source location
            self.probe_map.insert((block.file, block.line), probe_id);
        }
        CoverageMap::new(self.probe_map.clone())
    }
}
```

#### Step 2: Runtime Coverage Collection
```rust
// src/runtime/coverage.rs (new)
pub struct CoverageCollector {
    /// Tracks which probes were hit
    hit_probes: Arc<Mutex<HashSet<ProbeId>>>,
}

impl CoverageCollector {
    /// Called by CoverageProbe MIR instruction
    pub fn record_probe(&self, probe_id: ProbeId) {
        self.hit_probes.lock().unwrap().insert(probe_id);
    }

    /// Export coverage data in LCOV format
    pub fn export_lcov(&self, map: &CoverageMap) -> String {
        let mut lcov = String::new();
        for ((file, line), probe_id) in map.probes() {
            let hit = if self.hit_probes.lock().unwrap().contains(&probe_id) { 1 } else { 0 };
            lcov.push_str(&format!("DA:{},{}\n", line, hit));
        }
        lcov
    }
}
```

#### Step 3: Integration with Test Runner
```simple
# simple/std_lib/src/spec/coverage.spl
module spec.coverage:

    # Enable coverage collection
    fn enable_coverage():
        __builtin_coverage_start()

    # Write coverage report
    fn write_coverage_report(path: String):
        val data = __builtin_coverage_collect()
        File.write(path, data.to_lcov())

    # Integrate with spec runner
    impl Runner:
        fn run_with_coverage(suite: Suite, output_path: String):
            enable_coverage()
            val results = suite.run()
            write_coverage_report(output_path)
            results
```

#### Step 4: HTML Report Generation
```rust
// Extend simple_mock_helper to parse Simple coverage
// src/util/simple_mock_helper/src/simple_coverage.rs (new)
pub struct SimpleCoverageReport {
    /// Per-file line coverage
    files: HashMap<PathBuf, FileCoverage>,
}

impl SimpleCoverageReport {
    /// Parse LCOV from Simple runtime
    pub fn from_lcov(lcov: &str) -> Self { ... }

    /// Generate HTML report (merge with Rust coverage)
    pub fn to_html(&self, rust_cov: &LlvmCovExport) -> String { ... }
}
```

**Alternative: Source Mapping**
- Map MIR back to `.spl` source lines
- Use existing LLVM coverage infrastructure
- Lower implementation cost, less accuracy

**Effort**: High (2-3 weeks)
**Dependencies**: MIR instrumentation pass, runtime support
**Files**:
- `src/compiler/coverage.rs` (instrumentation)
- `src/runtime/coverage.rs` (collection)
- `simple/std_lib/src/spec/coverage.spl` (Simple API)
- `src/util/simple_mock_helper/src/simple_coverage.rs` (reporting)

---

### 2.3 Benchmarking Framework ✅ Priority: 🟡 Medium
**Current State**: No performance benchmarking
**Gap**: Can't track performance regressions

**Implementation Strategy**:

#### Option A: Integrate Criterion.rs (Recommended for MVP)
```rust
// benches/simple_benchmarks.rs (new)
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use simple_driver::Driver;

fn bench_parser(c: &mut Criterion) {
    let source = std::fs::read_to_string("benches/fixtures/large_file.spl").unwrap();
    c.bench_function("parse_large_file", |b| {
        b.iter(|| {
            let driver = Driver::new();
            driver.parse(black_box(&source))
        })
    });
}

criterion_group!(benches, bench_parser);
criterion_main!(benches);
```

#### Option B: Native Simple Benchmarking Library
```simple
# simple/std_lib/src/bench/mod.spl
module bench:

    # Benchmark suite
    class Suite:
        val name: String
        val benchmarks: [Benchmark]

        fn run() -> Report:
            benchmarks.map(\b: b.run()).aggregate()

    # Single benchmark
    class Benchmark:
        val name: String
        val iterations: Int = 1000
        val warmup: Int = 100

        fn run() -> BenchmarkResult:
            # Warmup
            for _ in 0..warmup:
                execute()

            # Measure
            val start = Time.now()
            for _ in 0..iterations:
                execute()
            val duration = Time.now() - start

            BenchmarkResult.new(name, duration / iterations)

        fn execute():
            # Implemented by user

    # DSL for benchmarks
    fn benchmark(name: String, block: fn()):
        Benchmark.new(name, 1000, 100, block)
```

**Example Usage**:
```simple
# benches/parser_bench.spl
import bench.*

describe "Parser Benchmarks":
    benchmark "parse small file", \:
        val source = File.read("fixtures/small.spl")
        Parser.parse(source)

    benchmark "parse large file", \:
        val source = File.read("fixtures/large.spl")
        Parser.parse(source)
```

**Recommendation**: Start with **Option A** (Criterion.rs) for immediate value, implement **Option B** later for dogfooding.

**Effort**: Medium (5-7 days)
**Files**:
- `benches/` (new directory with Criterion benchmarks)
- `simple/std_lib/src/bench/` (future native library)
- `.github/workflows/benchmarks.yml` (CI integration)
- `doc/guide/benchmarking.md` (user guide)

---

## Phase 3: Quality Enhancements (Medium Impact, Medium Effort)
**Duration**: 4-5 weeks
**Goal**: Advanced testing capabilities

### 3.1 Enhanced Test Reporting Dashboard ✅ Priority: 🟡 Medium
**Current State**: Basic HTML coverage reports exist
**Gap**: No aggregated view across test levels, no historical trends

**Implementation Strategy**:

#### Backend: Unified Test Report API
```rust
// src/util/simple_mock_helper/src/dashboard.rs (new)
pub struct TestDashboard {
    /// Aggregated test results
    results: Vec<TestResult>,
    /// Coverage by level
    coverage: HashMap<TestLevel, CoverageData>,
    /// Historical trends
    history: Vec<HistoricalSnapshot>,
}

impl TestDashboard {
    /// Collect all test data
    pub fn collect() -> Self {
        let results = Self::collect_test_results();
        let coverage = Self::collect_coverage_data();
        let history = Self::load_history();
        TestDashboard { results, coverage, history }
    }

    /// Export to JSON for web dashboard
    pub fn to_json(&self) -> String { ... }

    /// Export to HTML
    pub fn to_html(&self) -> String { ... }
}
```

#### Frontend: Web Dashboard (Simple + Electron)
```simple
# simple/std_lib/src/dashboard/app.spl
module dashboard:

    # Dashboard application
    class App:
        val data: DashboardData

        fn render() -> Html:
            html """
            <div class="dashboard">
                <section class="summary">
                    {render_summary()}
                </section>
                <section class="coverage">
                    {render_coverage_grid()}
                </section>
                <section class="trends">
                    {render_trend_charts()}
                </section>
            </div>
            """

        fn render_coverage_grid() -> Html:
            html """
            <table>
                <tr>
                    <th>Level</th>
                    <th>Branch %</th>
                    <th>Function %</th>
                    <th>Class %</th>
                </tr>
                {for level in TestLevel.all():
                    render_coverage_row(level)
                }
            </table>
            """
```

**Features**:
1. **Test Results Grid**: Pass/fail/skip by test level
2. **Coverage Matrix**: Branch/Function/Class coverage per level
3. **Trend Charts**: Historical coverage over time (Chart.js)
4. **Failure Analysis**: Top failing tests, flaky test detection
5. **Performance Metrics**: Test execution time trends

**Effort**: Medium (1.5-2 weeks)
**Files**:
- `src/util/simple_mock_helper/src/dashboard.rs` (backend)
- `simple/std_lib/src/dashboard/` (frontend app)
- `target/dashboard/index.html` (generated report)
- `Makefile` (add `make dashboard` target)

---

### 3.2 Fuzzing Infrastructure ✅ Priority: 🟡 Medium
**Current State**: Unknown (needs investigation)
**Gap**: No systematic fuzzing for parser/compiler

**Investigation First**:
```bash
# Check if fuzzing exists
find /home/ormastes/dev/pub/simple -name "*fuzz*" -o -name "*.fuzz" -o -name "afl*"
grep -r "cargo-fuzz\|libFuzzer\|afl" .
```

**Implementation Strategy** (if missing):

#### Option A: Cargo-Fuzz (Recommended)
```rust
// fuzz/fuzz_targets/parser.rs (new)
#![no_main]
use libfuzzer_sys::fuzz_target;
use simple_parser::Parser;

fuzz_target!(|data: &[u8]| {
    if let Ok(source) = std::str::from_utf8(data) {
        let parser = Parser::new();
        let _ = parser.parse(source); // Should never panic
    }
});
```

**Fuzz Targets**:
1. **Parser**: Arbitrary source code → AST
2. **HIR Lowering**: AST → HIR (should preserve semantics)
3. **MIR Generation**: HIR → MIR (should be valid)
4. **Codegen**: MIR → Cranelift IR (should compile)
5. **Runtime**: Bytecode execution (should not segfault)

#### Setup
```bash
# Install cargo-fuzz
cargo install cargo-fuzz

# Create fuzz directory
cargo fuzz init

# Run fuzzer (continuous)
cargo fuzz run parser -- -max_total_time=3600

# Minimize corpus
cargo fuzz cmin parser
```

**CI Integration**:
```yaml
# .github/workflows/fuzz.yml
name: Fuzzing
on:
  schedule:
    - cron: '0 2 * * *'  # Nightly at 2 AM
jobs:
  fuzz:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - name: Install cargo-fuzz
        run: cargo install cargo-fuzz
      - name: Run fuzzers (1 hour each)
        run: |
          cargo fuzz run parser -- -max_total_time=3600
          cargo fuzz run hir_lowering -- -max_total_time=3600
      - name: Upload crashes
        if: failure()
        uses: actions/upload-artifact@v3
        with:
          name: fuzz-crashes
          path: fuzz/artifacts/**/*
```

**Effort**: Medium (1 week for setup + ongoing)
**Files**:
- `fuzz/fuzz_targets/` (fuzzing targets)
- `fuzz/corpus/` (seed inputs)
- `.github/workflows/fuzz.yml` (CI)

---

### 3.3 Mutation Testing ✅ Priority: 🟢 Low
**Current State**: None
**Gap**: Can't validate test suite quality

**Implementation Strategy**:

#### Option A: Cargo-Mutants (Recommended)
```bash
# Install
cargo install cargo-mutants

# Run mutation testing
cargo mutants -- --workspace

# Generate report
cargo mutants --output mutants.json -- --workspace
```

**Configuration**:
```toml
# Cargo.toml
[package.metadata.mutants]
# Exclude generated code
exclude_files = ["src/generated/*", "target/*"]
# Focus on critical modules
include_files = ["src/parser/*", "src/compiler/*"]
# Timeout per mutant
timeout = 300
```

**CI Integration** (expensive, run weekly):
```yaml
# .github/workflows/mutation-testing.yml
name: Mutation Testing
on:
  schedule:
    - cron: '0 3 * * 0'  # Weekly Sunday 3 AM
jobs:
  mutants:
    runs-on: ubuntu-latest
    timeout-minutes: 360  # 6 hours max
    steps:
      - uses: actions/checkout@v4
      - name: Run mutation testing
        run: |
          cargo install cargo-mutants
          cargo mutants --output mutants.json -- --workspace
      - name: Upload report
        uses: actions/upload-artifact@v3
        with:
          name: mutation-report
          path: mutants.json
```

#### Option B: Native Simple Mutator
```simple
# simple/std_lib/src/mutate/mod.spl
module mutate:

    # Mutation operators
    enum Mutation:
        ReplaceOperator(old: String, new: String)  # + -> -
        NegateCond(expr: Expr)                     # x > 0 -> x <= 0
        RemoveStatement(stmt: Stmt)                # Delete line
        ReplaceConstant(old: Any, new: Any)        # 0 -> 1

    # Mutate source code
    class Mutator:
        fn apply(source: String, mutation: Mutation) -> String

    # Run tests on mutant
    fn test_mutant(mutant: String, test_suite: Suite) -> MutantResult:
        val result = test_suite.run_on_code(mutant)
        if result.all_passed():
            MutantResult.survived(mutant)  # BAD: tests didn't catch mutation
        else:
            MutantResult.killed(mutant)    # GOOD: tests caught mutation
```

**Recommendation**: Use **Option A** (cargo-mutants) for Rust code, defer **Option B** until Simple is self-hosting.

**Effort**: Medium (5-7 days)
**Files**:
- `.cargo/config.toml` (mutants config)
- `.github/workflows/mutation-testing.yml` (CI)
- `doc/guide/mutation_testing.md` (user guide)

---

## Phase 4: Polish & Documentation (Low Impact, Low-Medium Effort)
**Duration**: 2-3 weeks
**Goal**: Document existing features, refine UX

### 4.1 Document Existing Features ✅ Priority: 🟢 Low
**Items**:
1. **Property-based testing** (`spec.property`)
2. **Snapshot testing** (`spec.snapshot`)
3. **Architecture compliance** (`spec.arch`)

**Tasks**:
```simple
# doc/guide/property_based_testing.md (new, ~500 lines)
# Property-Based Testing in Simple
## Introduction
Property-based testing verifies code properties hold for randomly generated inputs...

## Quick Start
import spec.property.*

describe "List.reverse":
    it "is involutive (reverse(reverse(x)) == x)":
        property(\xs: [Int]:
            expect(xs.reverse().reverse()).to(eq(xs))
        ).check(iterations: 1000)

## Generators
...
```

**Effort**: Low (1 week total)
**Files**:
- `doc/guide/property_based_testing.md` (new)
- `doc/guide/snapshot_testing.md` (new)
- `doc/guide/architecture_testing.md` (new)
- Update `README.md` with links

---

### 4.2 Snapshot Testing Enhancements ✅ Priority: 🟢 Low
**Current State**: `spec.snapshot` exists but may need polish
**Enhancements**:
1. Interactive snapshot update mode (`--update-snapshots`)
2. Visual diff for HTML/image snapshots
3. Git integration (auto-commit approved snapshots)

**Effort**: Low (3-4 days)

---

## Implementation Timeline

```
Week 1-2:   Phase 1 (Quick Wins)
            ├─ Mock prevention for Simple ✓
            ├─ Deployment verification ✓
            └─ Contract testing ✓

Week 3-6:   Phase 2 (Foundations)
            ├─ Mock library for Simple ✓
            ├─ Coverage for Simple source ✓
            └─ Benchmarking framework ✓

Week 7-11:  Phase 3 (Enhancements)
            ├─ Test dashboard ✓
            ├─ Fuzzing infrastructure ✓
            └─ Mutation testing ✓

Week 12-14: Phase 4 (Polish)
            ├─ Documentation ✓
            └─ Snapshot enhancements ✓
```

---

## Dependencies & Blockers

### Critical Dependencies
1. **Mock library for Simple** requires:
   - Reflection API in Simple runtime (or macro system)
   - Decision: reflection-based vs. macro-based approach

2. **Coverage for Simple** requires:
   - MIR instrumentation pass
   - Runtime coverage collection
   - LCOV export from Simple runtime

3. **Fuzzing** requires:
   - Investigation of current status first
   - Corpus seed creation

### Resource Requirements
- **Development Time**: ~14 weeks for full roadmap
- **Infrastructure**: CI/CD runner time (fuzzing/mutation testing expensive)
- **Storage**: Benchmark history, mutation reports, snapshot storage

---

## Success Metrics

### Phase 1 (Quick Wins)
- [ ] Mock policy enforcement active for all Simple tests
- [ ] Deployment smoke tests run in CI
- [ ] Contract tests prevent API breakage

### Phase 2 (Foundations)
- [ ] 80%+ Simple code has mock-based unit tests
- [ ] Coverage reports show `.spl` file coverage
- [ ] Benchmarks run nightly, detect regressions

### Phase 3 (Enhancements)
- [ ] Dashboard shows aggregated test health
- [ ] Fuzzing finds 0 crashes in 24-hour runs
- [ ] Mutation score >80%

### Phase 4 (Polish)
- [ ] All testing features documented
- [ ] Snapshot workflow smooth (1-command update)

---

## Prioritization Matrix (Updated)

| Component | Phase | Effort | Impact | Status |
|-----------|-------|--------|--------|--------|
| Mock prevention (Simple) | 1 | Low | High | ❌ Missing |
| Deployment verification | 1 | Low | High | ❌ Missing |
| Contract testing | 1 | Low | Medium | ❌ Missing |
| Mock library (Simple) | 2 | Medium | High | ❌ Missing |
| Coverage (Simple) | 2 | High | High | ❌ Missing |
| Benchmarking | 2 | Medium | Medium | ❌ Missing |
| Test dashboard | 3 | Medium | Low | ⚠️ Basic |
| Fuzzing | 3 | Medium | High | ❓ Unknown |
| Mutation testing | 3 | Medium | Medium | ❌ Missing |
| Property-based docs | 4 | Low | Low | ✅ Exists (needs docs) |
| Snapshot enhancements | 4 | Low | Low | ✅ Exists (needs polish) |
| Arch compliance | - | - | - | ✅ Complete |

---

## Next Steps

1. **Immediate**: Investigate fuzzing status (30 min)
2. **Week 1**: Implement mock prevention for Simple (Phase 1.1)
3. **Week 1**: Set up deployment verification (Phase 1.2)
4. **Week 2**: Build contract testing foundation (Phase 1.3)
5. **Week 3+**: Begin Phase 2 (mock library design decision)

---

## Appendix A: Technology Choices

### Mock Library
- **Reflection-based**: Flexible, runtime overhead, easier to start
- **Macro-based**: Fast, compile-time checked, more complex

**Recommendation**: Start with reflection, migrate to macros later

### Coverage
- **MIR instrumentation**: Accurate, low overhead, requires compiler changes
- **Source mapping**: Less accurate, reuses LLVM infra, faster to implement

**Recommendation**: MIR instrumentation for accuracy

### Benchmarking
- **Criterion.rs**: Mature, statistical rigor, Rust-only
- **Native Simple**: Dogfooding, less mature, better integration

**Recommendation**: Criterion.rs for MVP, native later

---

## Appendix B: Alternative Approaches

### Mock Library Alternatives
1. **Manual test doubles** - No framework, just write fake implementations
2. **Trait-based dependency injection** - Use interfaces, no mocking needed
3. **Record/replay** - Record real calls, replay in tests

### Coverage Alternatives
1. **Source-to-source transformation** - Inject counters in AST
2. **Bytecode instrumentation** - Instrument at runtime
3. **Sampling profiler** - Statistical coverage (imprecise)

---

**Maintained by**: Development Team
**Review Cycle**: Monthly
**Last Updated**: 2026-01-21
