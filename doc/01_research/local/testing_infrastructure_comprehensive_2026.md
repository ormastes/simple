# Comprehensive Testing Infrastructure Research for Simple

**Research Date:** 2026-01-21
**Status:** Comprehensive Analysis
**Scope:** 6 testing patterns - implementation status and recommendations

## Executive Summary

| Pattern | Status in Simple | External Tools | Recommendation | Priority |
|---------|-----------------|----------------|----------------|----------|
| **Property-Based Testing** | ✅ **Implemented** | QuickCheck, Hypothesis | Use existing | N/A |
| **Snapshot Testing** | ✅ **Implemented** | Jest, insta | Use existing | N/A |
| **Benchmarking** | 🟡 Partial (tree-sitter only) | Criterion, hyperfine | Expand stdlib | High |
| **Mock Library** | ❌ Not Implemented | Mockito, Sinon | Build from scratch | Medium |
| **Contract Testing (HTTP)** | ❌ Not Implemented | Pact, Spring Cloud Contract | Build from scratch | Low |
| **Deployment Verification** | 🟡 Infrastructure only | Flagger, Harness | Add smoke/canary tests | Medium |

---

## 1. Property-Based Testing

### 1.1 Status: ✅ IMPLEMENTED

**Location:** `src/lib/std/src/spec/property/runner.spl`

**Capabilities:**
- Generator-based random input generation
- Shrinking to minimal failing cases
- Configurable iterations and timeouts
- Integration with SSpec test framework

### 1.2 Existing Implementation

```simple
# From: src/lib/std/src/spec/property/runner.spl

pub fn run_property_test<T>(
    test_fn: fn(T) -> bool,
    generator: impl Generator<T>,
    config: PropertyConfig
) -> PropertyTestResult<T>

# Convenience functions:
pub fn check_property<T>(property: fn(T) -> bool, generator: impl Generator<T>) -> bool
pub fn quick_check<T>(property: fn(T) -> bool, generator: impl Generator<T>) -> bool
pub fn thorough_check<T>(property: fn(T) -> bool, generator: impl Generator<T>) -> bool
```

**Features:**
- ✅ Random input generation via generators
- ✅ Automatic shrinking to minimal failing case
- ✅ Timeout support (per iteration and total)
- ✅ Verbose mode for debugging
- ✅ Seed support for reproducibility
- ✅ Thread-based timeout isolation

### 1.3 Comparison with External Tools

| Feature | Simple (std.spec.property) | QuickCheck (Haskell) | Hypothesis (Python) | PropTest (Rust) |
|---------|---------------------------|----------------------|---------------------|-----------------|
| Generators | ✅ Custom trait | ✅ Arbitrary typeclass | ✅ Strategies | ✅ Arbitrary trait |
| Shrinking | ✅ Automatic | ✅ Automatic | ✅ Advanced (reduce) | ✅ Automatic |
| Stateful testing | ❌ Not yet | ✅ monadic | ✅ StateMachine | ✅ prop_state_machine |
| Regression DB | ❌ Not yet | ❌ No | ✅ .hypothesis dir | ❌ No |
| Integration | ✅ SSpec | - | ✅ pytest | ✅ cargo test |

### 1.4 Example Usage

```simple
# Existing API
import std.spec.property.runner

describe "List operations":
    it "reverse is involution":
        val property = \xs: xs.reverse().reverse() == xs
        val gen = generators.list(generators.i32())
        val result = run_property_test(property, gen, PropertyConfig.default())
        expect result.is_success()
```

### 1.5 Recommendations

**✅ COMPLETE** - No action needed, existing implementation is comprehensive.

**Optional enhancements:**
1. Add stateful property testing (state machine testing)
2. Implement regression database (save failing cases)
3. Add more built-in generators (tuples, enums, custom types)
4. Improve shrinking strategies (targeted shrinking)

---

## 2. Snapshot Testing

### 2.1 Status: ✅ IMPLEMENTED

**Location:** `src/lib/std/src/spec/snapshot/`

**Modules:**
- `runner.spl` - Test execution engine
- `storage.spl` - Snapshot file management
- `formats.spl` - Serialization formats (JSON, text, custom)
- `comparison.spl` - Diff algorithms
- `config.spl` - Configuration management

### 2.2 Existing Implementation

```simple
# From: src/lib/std/src/spec/snapshot/runner.spl

pub fn expect_snapshot(
    value: Any,
    config: SnapshotConfig
) -> SnapshotTestResult

# Result types
pub enum SnapshotTestResult:
    Pass(test_name: text)
    Fail(test_name: text, diff: text)
    Updated(test_name: text)
    Created(test_name: text)
```

**Features:**
- ✅ Multiple output formats (JSON, text, custom)
- ✅ Snapshot normalization (timestamps, IDs)
- ✅ Custom normalizers
- ✅ Update mode (--snapshot-update)
- ✅ Diff generation
- ✅ Snapshot directory configuration

### 2.3 Comparison with External Tools

| Feature | Simple (std.spec.snapshot) | Jest (JS) | insta (Rust) | pytest (Python) |
|---------|---------------------------|-----------|--------------|-----------------|
| Inline snapshots | ❌ Not yet | ✅ Yes | ✅ Yes | ❌ No |
| Update mode | ✅ CLI flag | ✅ -u flag | ✅ cargo insta | ✅ --snapshot-update |
| Review UI | ❌ Not yet | ❌ No | ✅ cargo insta review | ❌ No |
| Formats | ✅ JSON, text, custom | ✅ Any serializable | ✅ Any Debug/Serialize | ✅ Any |
| Normalization | ✅ Timestamps, IDs, custom | ❌ Manual | ✅ Redactions | ✅ Manual |
| Binary snapshots | ❌ Not yet | ❌ No | ✅ Yes | ✅ Yes |

### 2.4 Example Usage

```simple
# Existing API
import std.spec.snapshot

describe "API responses":
    it "returns user list":
        val response = api.get_users()
        val config = SnapshotConfig(
            format: SnapshotFormat::Json,
            normalize: true,
            normalize_timestamps: true
        )
        expect_snapshot(response, config)
```

### 2.5 Recommendations

**✅ MOSTLY COMPLETE** - Well-designed, production-ready.

**Optional enhancements:**
1. Add inline snapshot support (embed snapshots in source)
2. Build TUI review tool (like `cargo insta review`)
3. Support binary snapshots (images, PDFs)
4. Add snapshot diff visualization (HTML reports)

---

## 3. Benchmarking

### 3.1 Status: 🟡 PARTIAL IMPLEMENTATION

**Location:** `src/lib/std/src/parser/treesitter/benchmark.spl`

**Current Scope:** Tree-sitter parser benchmarking only

### 3.2 Existing Implementation

```simple
# From: src/lib/std/src/parser/treesitter/benchmark.spl

class BenchmarkResult:
    name: text
    iterations: i32
    total_time_ms: f32
    avg_time_ms: f32
    min_time_ms: f32
    max_time_ms: f32
    lines_of_code: i32

fn benchmark_parse(source: text, iterations: i32) -> BenchmarkResult
fn benchmark_incremental_parse(original: text, modified: text, iterations: i32) -> BenchmarkResult
fn benchmark_query(source: text, iterations: i32) -> BenchmarkResult
```

**Limitations:**
- ❌ Tree-sitter specific (not general-purpose)
- ❌ No statistical outlier detection
- ❌ No warmup phase
- ❌ No comparison mode
- ❌ No regression tracking

### 3.3 Comparison with External Tools

| Feature | Simple (current) | Criterion (Rust) | hyperfine (CLI) | pytest-benchmark (Python) |
|---------|-----------------|------------------|-----------------|---------------------------|
| **Target** | Tree-sitter only | Rust microbenchmarks | CLI commands | Python functions |
| **Warmup** | ❌ No | ✅ Configurable | ✅ Automatic | ✅ Calibration |
| **Outlier detection** | ❌ No | ✅ Statistical | ✅ Automatic | ✅ Statistical |
| **Comparison** | ❌ Manual | ✅ Baseline comparison | ✅ Multiple commands | ✅ Compare groups |
| **Regression** | ❌ No | ✅ History tracking | ❌ No | ✅ Storage backend |
| **Output** | ❌ Text only | ✅ Plots, HTML | ✅ Markdown, JSON | ✅ JSON, histogram |
| **Statistical rigor** | ❌ Basic avg/min/max | ✅ Confidence intervals | ✅ Parametric tests | ✅ Confidence intervals |

### 3.4 External Tool Details

#### hyperfine (Command-line benchmarking)
**What it is:** A command-line benchmarking tool written in Rust.

**Key Features:**
- Automatically performs warmup runs
- Detects statistical outliers
- Corrects for shell spawning time
- Compares multiple commands
- Exports to JSON, Markdown, CSV

**Typical usage:**
```bash
# Compare two implementations
hyperfine 'python old_script.py' 'python new_script.py'

# With warmup and parameters
hyperfine --warmup 3 --parameter-scan num_threads 1 16 './benchmark {num_threads}'
```

#### Criterion (Rust microbenchmarking)
**What it is:** A statistics-driven benchmarking library for Rust.

**Key Features:**
- Detects performance regressions
- Generates HTML reports with plots
- Statistical outlier detection
- Configurable sample size and confidence intervals
- Baseline comparison

**Typical usage:**
```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn benchmark_fibonacci(c: &mut Criterion) {
    c.bench_function("fib 20", |b| b.iter(|| fibonacci(black_box(20))));
}

criterion_group!(benches, benchmark_fibonacci);
criterion_main!(benches);
```

### 3.5 Recommended Design for Simple

**Goal:** General-purpose benchmarking library for Simple programs.

#### API Design

```simple
# simple/std_lib/src/testing/benchmark.spl

import std.time

# Benchmark configuration
struct BenchmarkConfig:
    warmup_iterations: i32        # Default: 3
    measurement_iterations: i32   # Default: 100
    measurement_time_secs: f64    # Default: 5.0
    sample_size: i32              # Default: 10
    outlier_threshold: f64        # Default: 3.0 (std devs)
    confidence_level: f64         # Default: 0.95

    static fn default() -> BenchmarkConfig:
        BenchmarkConfig(
            warmup_iterations: 3,
            measurement_iterations: 100,
            measurement_time_secs: 5.0,
            sample_size: 10,
            outlier_threshold: 3.0,
            confidence_level: 0.95
        )

    static fn quick() -> BenchmarkConfig:
        """Fast benchmarking (less accurate)."""
        BenchmarkConfig.default().with(
            warmup_iterations: 1,
            sample_size: 3
        )

# Benchmark statistics
struct BenchmarkStats:
    mean_ns: f64
    median_ns: f64
    std_dev_ns: f64
    min_ns: f64
    max_ns: f64
    outliers_low: i32
    outliers_high: i32
    samples: List<f64>

    fn format_time(ns: f64) -> text:
        """Format nanoseconds to human-readable."""
        if ns < 1000.0:
            "{ns:.2f} ns"
        elif ns < 1000000.0:
            "{ns / 1000.0:.2f} μs"
        elif ns < 1000000000.0:
            "{ns / 1000000.0:.2f} ms"
        else:
            "{ns / 1000000000.0:.2f} s"

    fn summary() -> text:
        """Human-readable summary."""
        val mean_str = BenchmarkStats.format_time(self.mean_ns)
        val median_str = BenchmarkStats.format_time(self.median_ns)
        val std_dev_str = BenchmarkStats.format_time(self.std_dev_ns)

        """
        Mean:   {mean_str} ± {std_dev_str}
        Median: {median_str}
        Range:  [{BenchmarkStats.format_time(self.min_ns)} .. {BenchmarkStats.format_time(self.max_ns)}]
        Outliers: {self.outliers_low} low, {self.outliers_high} high
        """

# Main benchmarking function
pub fn benchmark(
    name: text,
    func: fn(),
    config: BenchmarkConfig = BenchmarkConfig.default()
) -> BenchmarkStats:
    """
    Benchmark a function.

    Args:
        name: Benchmark name for reporting
        func: Function to benchmark (takes no args)
        config: Benchmark configuration

    Returns:
        Statistical results

    Example:
        val stats = benchmark("fibonacci", \: fibonacci(20))
        print stats.summary()
    """

    # Warmup phase
    for _ in 0..config.warmup_iterations:
        func()

    # Measurement phase
    var samples = []
    for _ in 0..config.sample_size:
        var sample_times = []

        val sample_start = time.now_nanos()
        var elapsed_ns = 0.0

        while sample_times.len() < config.measurement_iterations and
              elapsed_ns < config.measurement_time_secs * 1_000_000_000.0:
            val start = time.now_nanos()
            func()
            val end = time.now_nanos()

            val duration = end - start
            sample_times.append(duration)
            elapsed_ns = end - sample_start

        # Calculate median for this sample
        sample_times.sort()
        val median = sample_times[sample_times.len() / 2]
        samples.append(median)

    # Calculate statistics
    calculate_stats(samples, config.outlier_threshold)

# Comparison benchmarking
pub fn compare(
    benchmarks: Map<text, fn()>,
    config: BenchmarkConfig = BenchmarkConfig.default()
) -> Map<text, BenchmarkStats>:
    """
    Compare multiple implementations.

    Example:
        val results = compare({
            "old": \: old_algorithm(),
            "new": \: new_algorithm()
        })

        for (name, stats) in results:
            print "{name}: {stats.summary()}"
    """
    var results = {}
    for (name, func) in benchmarks:
        results[name] = benchmark(name, func, config)
    results

# Integration with SSpec
pub fn bench_spec(
    name: text,
    func: fn(),
    baseline: Option<BenchmarkStats> = None
):
    """
    Run benchmark as a spec test.

    Example:
        describe "Performance":
            bench_spec("sorting 1000 items",
                \: sort(generate_list(1000))
            )
    """
    it name:
        val stats = benchmark(name, func)
        print stats.summary()

        # Fail if regression detected
        if baseline.is_some():
            val base = baseline.unwrap()
            val regression_threshold = 1.1  # 10% slower is regression
            if stats.mean_ns > base.mean_ns * regression_threshold:
                val pct = ((stats.mean_ns / base.mean_ns - 1.0) * 100.0) as i32
                expect false, "Performance regression: {pct}% slower than baseline"

# Helper: Calculate statistics
fn calculate_stats(samples: List<f64>, outlier_threshold: f64) -> BenchmarkStats:
    val n = samples.len() as f64
    val mean = samples.sum() / n
    val variance = samples.map(\x: (x - mean) ** 2.0).sum() / n
    val std_dev = math.sqrt(variance)

    # Detect outliers (beyond threshold standard deviations)
    var outliers_low = 0
    var outliers_high = 0
    for sample in samples:
        if sample < mean - outlier_threshold * std_dev:
            outliers_low += 1
        elif sample > mean + outlier_threshold * std_dev:
            outliers_high += 1

    # Median
    var sorted = samples.clone()
    sorted.sort()
    val median = sorted[sorted.len() / 2]

    BenchmarkStats(
        mean_ns: mean,
        median_ns: median,
        std_dev_ns: std_dev,
        min_ns: sorted[0],
        max_ns: sorted[sorted.len() - 1],
        outliers_low: outliers_low,
        outliers_high: outliers_high,
        samples: samples
    )

# Export
export benchmark
export compare
export bench_spec
export BenchmarkConfig
export BenchmarkStats
```

#### Usage Examples

**Example 1: Simple benchmark**
```simple
import std.testing.benchmark as bench

fn main():
    val stats = bench.benchmark("fibonacci", \: fibonacci(30))
    print stats.summary()
    # Output:
    # Mean:   145.23 ms ± 2.31 ms
    # Median: 144.98 ms
    # Range:  [142.11 ms .. 151.45 ms]
    # Outliers: 0 low, 1 high
```

**Example 2: Compare implementations**
```simple
import std.testing.benchmark as bench

describe "Sorting algorithms":
    it "compares quicksort vs mergesort":
        val data = generate_random_list(10000)

        val results = bench.compare({
            "quicksort": \: quicksort(data.clone()),
            "mergesort": \: mergesort(data.clone()),
            "bubblesort": \: bubblesort(data.clone())
        })

        # Results automatically printed
        # quicksort: Mean: 5.23 ms ± 0.12 ms
        # mergesort: Mean: 6.11 ms ± 0.18 ms
        # bubblesort: Mean: 523.45 ms ± 12.34 ms

        # Assert performance requirements
        expect results["quicksort"].mean_ns < 10_000_000.0  # < 10ms
```

**Example 3: Regression detection**
```simple
import std.testing.benchmark as bench

describe "Performance regressions":
    it "maintains O(n) complexity":
        val baseline = bench.benchmark("n=1000",
            \: process_items(1000))

        val current = bench.benchmark("n=10000",
            \: process_items(10000))

        # Should be ~10x slower (linear complexity)
        val ratio = current.mean_ns / baseline.mean_ns
        expect ratio < 15.0, "Complexity worse than O(n)"
```

### 3.6 Implementation Plan

**Phase 1: Core benchmarking (1 week)**
- [ ] Implement `BenchmarkConfig` and `BenchmarkStats`
- [ ] Implement `benchmark()` function with warmup
- [ ] Add outlier detection
- [ ] Write unit tests

**Phase 2: Comparison & reporting (3 days)**
- [ ] Implement `compare()` function
- [ ] Add summary formatting
- [ ] Generate JSON output

**Phase 3: SSpec integration (2 days)**
- [ ] Implement `bench_spec()`
- [ ] Add regression detection
- [ ] Write example specs

**Phase 4: Advanced features (1 week, optional)**
- [ ] Add histogram generation
- [ ] Implement baseline storage (JSON file)
- [ ] Add CLI command: `simple bench`
- [ ] Generate HTML reports

### 3.7 Recommendations

**Priority: HIGH**

✅ **Implement** `std.testing.benchmark` as general-purpose library

**Rationale:**
- Existing tree-sitter benchmark is too specific
- Performance testing is critical for compiler development
- Can reuse for stdlib benchmarking (sort, regex, etc.)
- Relatively simple to implement (~500 LOC)

---

## 4. Mock Library

### 4.1 Status: ❌ NOT IMPLEMENTED

**Location:** `test/lib/std/unit/spec/mock_spec.spl` (skeleton only, all tests skipped)

**Current State:** Design placeholder exists but no implementation.

### 4.2 Test Double Taxonomy

From Martin Fowler's "Mocks Aren't Stubs":

| Type | Purpose | Verification | Example |
|------|---------|--------------|---------|
| **Dummy** | Fill parameters | None | `User(id: 999, name: "dummy")` |
| **Stub** | Provide canned answers | State | `stub_db.get(id) -> Some(user)` |
| **Spy** | Record calls | State | `spy.was_called_with(42)` |
| **Mock** | Verify behavior | Behavior | `mock.expect_call("send", [email])` |
| **Fake** | Working but simplified | State | `InMemoryDatabase` |

**Key distinction:** Mocks use behavior verification (expect calls), others use state verification (check results).

### 4.3 Comparison with External Tools

| Feature | Mockito (Java) | Sinon (JS) | unittest.mock (Python) | Mockall (Rust) |
|---------|---------------|------------|------------------------|----------------|
| **Style** | Fluent API | Chainable | Class-based | Proc macros |
| **Stubs** | `when().thenReturn()` | `stub().returns()` | `return_value` | `expect().return_const()` |
| **Spies** | `spy()` on real objects | `spy()` wrapper | `wraps=` param | Not supported |
| **Arg matchers** | `any()`, `eq()`, custom | `match()` | `ANY`, `call()` | `eq()`, `with()` |
| **Call verification** | `verify().times()` | `calledOnce`, `calledWith` | `assert_called_with()` | `times()` |
| **Reset** | `reset()` | `resetHistory()` | `reset_mock()` | N/A (compile-time) |

### 4.4 Recommended Design for Simple

**Challenge:** Simple is a compiled language without runtime reflection, making mocking harder than in dynamic languages.

**Approach:** Trait-based mocking (similar to Rust's `mockall`).

#### API Design

```simple
# simple/std_lib/src/testing/mock.spl

# Base trait for all mocks
trait Mock:
    fn reset()
    fn verify() -> Result<(), text>

# Call record
struct CallRecord:
    method: text
    args: List<any>
    timestamp: f64

# Mock builder
class MockBuilder<T>:
    expectations: Map<text, List<Expectation>>
    stubs: Map<text, any>
    calls: List<CallRecord>

    static fn new() -> MockBuilder<T>:
        MockBuilder(
            expectations: {},
            stubs: {},
            calls: []
        )

    # Stub a method
    fn when(method: text) -> StubBuilder<T>:
        StubBuilder(mock: self, method: method)

    # Set expectation
    fn expect(method: text) -> ExpectationBuilder<T>:
        ExpectationBuilder(mock: self, method: method)

    # Verify all expectations met
    fn verify() -> Result<(), text>:
        for (method, expectations) in self.expectations:
            for expectation in expectations:
                if not expectation.is_satisfied(self.calls):
                    return Err("Expectation failed for {method}: {expectation}")
        Ok(())

    # Reset mock state
    fn reset():
        self.calls.clear()
        self.expectations.clear()
        self.stubs.clear()

# Stub builder (fluent API)
class StubBuilder<T>:
    mock: MockBuilder<T>
    method: text

    fn returns(value: any) -> MockBuilder<T>:
        self.mock.stubs[self.method] = value
        self.mock

    fn returns_once(value: any) -> MockBuilder<T>:
        # TODO: Implement one-time stubs
        self.mock

    fn throws(error: text) -> MockBuilder<T>:
        # TODO: Implement error stubs
        self.mock

# Expectation builder
class ExpectationBuilder<T>:
    mock: MockBuilder<T>
    method: text

    fn times(n: i32) -> MockBuilder<T>:
        val expectation = Expectation.Times(method: self.method, count: n)
        if self.method not in self.mock.expectations:
            self.mock.expectations[self.method] = []
        self.mock.expectations[self.method].append(expectation)
        self.mock

    fn once() -> MockBuilder<T>:
        self.times(1)

    fn never() -> MockBuilder<T>:
        self.times(0)

    fn with_args(args: List<any>) -> MockBuilder<T>:
        val expectation = Expectation.WithArgs(method: self.method, args: args)
        # ... similar to times()
        self.mock

# Expectations
enum Expectation:
    Times(method: text, count: i32)
    WithArgs(method: text, args: List<any>)
    AtLeast(method: text, min: i32)
    AtMost(method: text, max: i32)

    fn is_satisfied(calls: List<CallRecord>) -> bool:
        match self:
            Times(method, count):
                val actual = calls.filter(\c: c.method == method).len()
                actual == count
            WithArgs(method, expected_args):
                calls.any(\c: c.method == method and c.args == expected_args)
            # ... other cases

# Argument matchers
pub fn any() -> ArgMatcher:
    ArgMatcher::Any

pub fn eq(value: any) -> ArgMatcher:
    ArgMatcher::Eq(value)

pub fn gt(value: any) -> ArgMatcher:
    ArgMatcher::Gt(value)

pub fn contains(substring: text) -> ArgMatcher:
    ArgMatcher::Contains(substring)

enum ArgMatcher:
    Any
    Eq(any)
    Gt(any)
    Lt(any)
    Contains(text)
    OfType(text)
    Predicate(fn(any) -> bool)

# Convenience macro for creating mocks
macro mock!(T):
    """
    Create a mock for trait T.

    Example:
        val mock_db = mock!(Database)
        mock_db.when("get_user").returns(Some(user))
        mock_db.expect("save_user").once()
    """
    MockBuilder<T>.new()
```

#### Usage Examples

**Example 1: Simple stubbing**
```simple
import std.testing.mock

trait Database:
    fn get_user(id: i32) -> Option<User>
    fn save_user(user: User) -> Result<(), text>

describe "UserService with mocks":
    it "fetches user from database":
        # Create mock
        val mock_db = mock!(Database)

        # Stub method
        mock_db.when("get_user")
            .returns(Some(User(id: 1, name: "Alice")))

        # Use mock
        val service = UserService(db: mock_db)
        val user = service.find_user(1)

        expect user.is_some()
        expect user.unwrap().name == "Alice"
```

**Example 2: Verify calls**
```simple
import std.testing.mock

describe "Email service":
    it "sends email on user registration":
        # Create mocks
        val mock_db = mock!(Database)
        val mock_email = mock!(EmailService)

        # Set expectations
        mock_db.expect("save_user").once()
        mock_email.expect("send_welcome_email")
            .once()
            .with_args([any(), eq("alice@example.com")])

        # Execute
        val service = RegistrationService(db: mock_db, email: mock_email)
        service.register("Alice", "alice@example.com")

        # Verify
        val result = mock_email.verify()
        expect result.is_ok()
```

**Example 3: Spy on real object**
```simple
import std.testing.mock

describe "Logger spy":
    it "logs errors":
        # Create spy (calls real implementation + records)
        val spy_logger = spy!(RealLogger.new())

        val service = DataProcessor(logger: spy_logger)
        service.process_invalid_data()

        # Verify logging happened
        expect spy_logger.was_called("log_error")
        expect spy_logger.call_count("log_error") == 1
```

### 4.5 Implementation Challenges

**Challenge 1: No runtime reflection**
- **Solution:** Require explicit mock trait implementation
- **Trade-off:** More boilerplate but type-safe

**Challenge 2: Method dispatch**
- **Solution:** Use trait objects with dynamic dispatch
- **Trade-off:** Slight performance cost (acceptable for tests)

**Challenge 3: Argument matching**
- **Solution:** Store arguments as `any` type
- **Trade-off:** Requires runtime type checking

### 4.6 Implementation Plan

**Phase 1: Core infrastructure (1 week)**
- [ ] Implement `MockBuilder` and `CallRecord`
- [ ] Add basic stubbing (`when().returns()`)
- [ ] Add call recording
- [ ] Write unit tests

**Phase 2: Expectations (1 week)**
- [ ] Implement `ExpectationBuilder`
- [ ] Add call count verification (`times()`, `once()`, `never()`)
- [ ] Add argument matching (`with_args()`)
- [ ] Test verification logic

**Phase 3: Argument matchers (3 days)**
- [ ] Implement `ArgMatcher` enum
- [ ] Add matchers: `any()`, `eq()`, `gt()`, `contains()`
- [ ] Add custom predicate matchers

**Phase 4: Advanced features (1 week, optional)**
- [ ] Add spy support (wrap real objects)
- [ ] Implement one-time stubs (`returns_once()`)
- [ ] Add error stubs (`throws()`)
- [ ] Generate mock report (calls, unmet expectations)

**Phase 5: Macro support (2 weeks, blocked on macro system)**
- [ ] Implement `mock!()` macro for auto-generation
- [ ] Add `spy!()` macro

### 4.7 Recommendations

**Priority: MEDIUM**

🟡 **Implement** basic mock library (Phase 1-3)

**Rationale:**
- Useful for testing stdlib (file I/O, network, etc.)
- Not critical (can use manual fakes for now)
- Moderate complexity (~800 LOC)
- Blocked on trait objects and `any` type support

**Alternative:** Use manual fakes for now, implement mocks later.

---

## 5. Contract Testing (HTTP/API)

### 5.1 Status: ❌ NOT IMPLEMENTED

**Note:** Simple has Design-by-Contract features (`in:`, `out:`, `invariant:`) for function contracts, but not HTTP/API contract testing.

**Location:** None (would be new: `std.testing.contract`)

### 5.2 What is Contract Testing?

**Consumer-Driven Contract Testing (CDC):** Ensures a provider API is compatible with consumer expectations without requiring full end-to-end integration tests.

**Key Concepts:**
1. **Consumer** writes tests defining expected API behavior
2. Tests generate a **contract** (JSON specification)
3. **Provider** validates they satisfy the contract
4. **Pact Broker** stores and versions contracts

**Benefits:**
- Test in isolation (no microservice dependencies)
- Catch breaking changes early
- Faster than end-to-end tests
- Self-documenting API contracts

### 5.3 Pact Workflow

```
Consumer Side:
┌──────────────┐
│ Consumer Test│  (JavaScript, Python, etc.)
└──────┬───────┘
       │ Generates
       ▼
┌──────────────┐
│   Contract   │  (JSON file)
│  Pact File   │
└──────┬───────┘
       │ Publishes to
       ▼
┌──────────────┐
│ Pact Broker  │  (Centralized registry)
└──────┬───────┘
       │ Fetches
       ▼
┌──────────────┐
│Provider Test │  (Verifies provider meets contract)
└──────────────┘
```

**Example Pact Contract (JSON):**
```json
{
  "consumer": {"name": "web-frontend"},
  "provider": {"name": "user-api"},
  "interactions": [
    {
      "description": "get user by ID",
      "request": {
        "method": "GET",
        "path": "/users/123"
      },
      "response": {
        "status": 200,
        "body": {
          "id": 123,
          "name": "Alice"
        }
      }
    }
  ]
}
```

### 5.4 Comparison with External Tools

| Feature | Pact (Multi-lang) | Spring Cloud Contract | Postman Contract Tests |
|---------|-------------------|----------------------|------------------------|
| **Approach** | Consumer-driven | Provider or consumer | Manual API tests |
| **Language support** | 15+ languages | JVM only | HTTP client |
| **Broker** | ✅ Pact Broker | ❌ No | ✅ Postman Cloud |
| **Matching** | Flexible (regex, types) | JSON path | Exact match |
| **Versioning** | ✅ Git-like | ❌ No | ❌ No |
| **CI integration** | ✅ Webhooks | ✅ Maven/Gradle | ✅ Newman CLI |
| **Message support** | ✅ Async messaging | ✅ Messaging | ❌ HTTP only |

### 5.5 Recommended Design for Simple

**Goal:** Lightweight Pact-compatible contract testing library.

#### API Design (Consumer Side)

```simple
# simple/std_lib/src/testing/contract.spl

import std.http

# Contract builder
class ContractBuilder:
    consumer: text
    provider: text
    interactions: List<Interaction>

    static fn new(consumer: text, provider: text) -> ContractBuilder:
        ContractBuilder(
            consumer: consumer,
            provider: provider,
            interactions: []
        )

    # Define an interaction
    fn given(state: text) -> InteractionBuilder:
        InteractionBuilder(contract: self, provider_state: state)

    # Save contract to file
    fn save(path: text) -> Result<(), text>:
        val json = self.to_pact_json()
        file.write(path, json)

# Interaction builder
class InteractionBuilder:
    contract: ContractBuilder
    provider_state: text
    description: text
    request: HttpRequest
    response: HttpResponse

    fn upon_receiving(description: text) -> InteractionBuilder:
        self.description = description
        self

    fn with_request(method: text, path: text) -> RequestBuilder:
        RequestBuilder(interaction: self, method: method, path: path)

# Request builder
class RequestBuilder:
    interaction: InteractionBuilder
    method: text
    path: text
    headers: Map<text, text>
    body: Option<any>

    fn with_header(key: text, value: text) -> RequestBuilder:
        self.headers[key] = value
        self

    fn with_body(body: any) -> RequestBuilder:
        self.body = Some(body)
        self

    fn will_respond_with() -> ResponseBuilder:
        ResponseBuilder(interaction: self.interaction)

# Response builder
class ResponseBuilder:
    interaction: InteractionBuilder
    status: i32
    headers: Map<text, text>
    body: Option<any>

    fn status(code: i32) -> ResponseBuilder:
        self.status = code
        self

    fn with_header(key: text, value: text) -> ResponseBuilder:
        self.headers[key] = value
        self

    fn with_body(body: any) -> ResponseBuilder:
        self.body = Some(body)
        self

    fn build() -> ContractBuilder:
        val interaction = Interaction(
            provider_state: self.interaction.provider_state,
            description: self.interaction.description,
            request: self.interaction.request,
            response: Response(
                status: self.status,
                headers: self.headers,
                body: self.body
            )
        )
        self.interaction.contract.interactions.append(interaction)
        self.interaction.contract

# Matchers (for flexible matching)
pub fn like(value: any) -> Matcher:
    """Match type, not exact value."""
    Matcher::Like(value)

pub fn each_like(value: any) -> Matcher:
    """Match array of objects with same structure."""
    Matcher::EachLike(value)

pub fn term(regex: text, example: text) -> Matcher:
    """Match regex pattern."""
    Matcher::Term(regex: regex, example: example)

enum Matcher:
    Like(any)
    EachLike(any)
    Term(regex: text, example: text)
    Integer
    String
    Boolean
```

#### Usage Examples (Consumer)

**Example 1: Define contract**
```simple
import std.testing.contract

describe "User API contract":
    it "gets user by ID":
        # Build contract
        val contract = ContractBuilder.new("web-app", "user-api")
            .given("user 123 exists")
            .upon_receiving("request for user 123")
            .with_request("GET", "/users/123")
            .will_respond_with()
            .status(200)
            .with_header("Content-Type", "application/json")
            .with_body({
                "id": like(123),  # Match type (integer)
                "name": like("Alice"),  # Match type (string)
                "email": term(r"^.+@.+\..+$", "alice@example.com")  # Match regex
            })
            .build()

        # Save contract
        contract.save("pacts/web-app-user-api.json")

        # Test with mock server
        val mock_server = contract.start_mock_server()
        val client = HttpClient.new()
        val response = client.get("{mock_server.url}/users/123")

        expect response.status == 200
        expect response.body["name"] == "Alice"

        mock_server.verify()  # Ensure all interactions matched
```

**Example 2: Publish to broker**
```simple
import std.testing.contract

fn main():
    val contract = ContractBuilder.new("web-app", "user-api")
        # ... define interactions

    # Publish to Pact Broker
    val broker = PactBroker.new("https://pact-broker.example.com")
    broker.publish(
        contract,
        version: "1.2.3",
        tags: ["main", "production"]
    )
```

#### API Design (Provider Side)

```simple
# Verify provider meets contracts

import std.testing.contract

describe "User API provider verification":
    it "satisfies web-app contract":
        val verifier = ContractVerifier.new()
            .with_provider("user-api")
            .with_broker("https://pact-broker.example.com")
            .with_consumer("web-app")
            .with_provider_base_url("http://localhost:8080")
            .with_state_setup(\state:
                # Setup provider state
                match state:
                    "user 123 exists":
                        db.insert(User(id: 123, name: "Alice"))
                    _:
                        pass
            )

        val result = verifier.verify()
        expect result.is_ok()
```

### 5.6 Implementation Plan

**Phase 1: Contract definition (1 week)**
- [ ] Implement `ContractBuilder`, `InteractionBuilder`
- [ ] Add fluent API for requests/responses
- [ ] Generate Pact JSON format
- [ ] Write unit tests

**Phase 2: Mock server (1 week)**
- [ ] Implement HTTP mock server
- [ ] Match requests to interactions
- [ ] Verify all interactions called
- [ ] Add matching logic (exact, regex, type)

**Phase 3: Provider verification (1 week)**
- [ ] Implement `ContractVerifier`
- [ ] Load contracts from files/broker
- [ ] Make HTTP requests to provider
- [ ] Compare responses to contract
- [ ] Add state setup hooks

**Phase 4: Pact Broker integration (1 week)**
- [ ] Implement `PactBroker` client
- [ ] Publish contracts (HTTP POST)
- [ ] Fetch contracts (HTTP GET)
- [ ] Support versioning and tags
- [ ] Implement webhooks for CI

**Phase 5: Matchers & advanced features (1 week, optional)**
- [ ] Implement flexible matchers (`like`, `term`, `each_like`)
- [ ] Add message contract support (async)
- [ ] Generate HTML reports
- [ ] Add CLI commands: `simple pact publish`, `simple pact verify`

### 5.7 Recommendations

**Priority: LOW**

⏸️ **Defer** contract testing library

**Rationale:**
- Not critical for compiler development
- Primarily useful for microservices/APIs
- Complex implementation (~1500 LOC + HTTP server)
- Requires HTTP client/server infrastructure
- Can use external Pact tools for now (pact-js, pact-python)

**Alternative:** For Simple web apps, use existing Pact libraries from other languages.

---

## 6. Deployment Verification

### 6.1 Status: 🟡 INFRASTRUCTURE ONLY

**Location:** `src/lib/std/src/tooling/deployment/pipeline.spl`

**Current Capabilities:**
- ✅ Environment enum (Dev, Staging, Production)
- ✅ Environment detection from strings
- ❌ No smoke tests
- ❌ No canary deployment support
- ❌ No blue-green deployment support

### 6.2 Deployment Testing Strategies

From industry best practices:

| Strategy | Description | Rollback Time | Blast Radius | Use Case |
|----------|-------------|---------------|--------------|----------|
| **Smoke Test** | Run critical tests post-deploy | Instant | Full (if fails) | Quick health check |
| **Canary** | Gradual traffic shift (5→25→50→100%) | < 1 minute | Small (5-10% users) | Risk mitigation |
| **Blue-Green** | Instant switch between environments | Instant | Full (if fails) | Zero-downtime |
| **A/B Test** | Split traffic by feature flag | Gradual | Controlled cohort | Feature validation |

### 6.3 Comparison with External Tools

| Feature | Flagger (K8s) | Harness | Spinnaker | LaunchDarkly |
|---------|--------------|---------|-----------|--------------|
| **Canary** | ✅ Automated | ✅ Automated | ✅ Automated | ✅ Flag-based |
| **Blue-Green** | ✅ Yes | ✅ Yes | ✅ Yes | ❌ No |
| **Smoke tests** | ✅ Webhooks | ✅ Built-in | ✅ Custom | ❌ No (flags only) |
| **Metrics** | ✅ Prometheus | ✅ Built-in | ✅ Custom | ✅ Analytics |
| **Rollback** | ✅ Automatic | ✅ Automatic | ✅ Manual/auto | ✅ Flag toggle |
| **Platform** | K8s only | Multi-cloud | Multi-cloud | Language SDK |

### 6.4 Deployment Verification Patterns

**Pattern 1: Smoke Tests**
Post-deployment health checks:
```simple
# Verify critical functionality
smoke_test("homepage loads", \: http.get("/").status == 200)
smoke_test("database connected", \: db.ping().is_ok())
smoke_test("API responds", \: api.health().status == "ok")
```

**Pattern 2: Canary Deployment**
Gradual rollout with metrics:
```
1. Deploy new version to 5% traffic
2. Monitor error rate, latency, CPU
3. If metrics OK → increase to 25%
4. Repeat until 100%
5. If metrics fail → rollback
```

**Pattern 3: Blue-Green Deployment**
Zero-downtime switch:
```
1. Deploy to "green" environment
2. Run smoke tests on green
3. Switch traffic: blue → green
4. Keep blue for rollback
```

### 6.5 Recommended Design for Simple

**Goal:** Deployment verification library for Simple applications.

#### API Design

```simple
# simple/std_lib/src/testing/deployment.spl

import std.http
import std.time
import tooling.deployment.pipeline.Environment

# Smoke test configuration
struct SmokeTestConfig:
    timeout_secs: f64           # Default: 30.0
    retry_attempts: i32         # Default: 3
    retry_delay_secs: f64       # Default: 5.0
    fail_fast: bool             # Default: true

    static fn default() -> SmokeTestConfig:
        SmokeTestConfig(
            timeout_secs: 30.0,
            retry_attempts: 3,
            retry_delay_secs: 5.0,
            fail_fast: true
        )

# Smoke test result
enum SmokeTestResult:
    Pass(test_name: text, duration_ms: f64)
    Fail(test_name: text, error: text, attempt: i32)
    Timeout(test_name: text)

# Smoke test suite
class SmokeTestSuite:
    tests: List<SmokeTest>
    config: SmokeTestConfig

    static fn new(config: SmokeTestConfig = SmokeTestConfig.default()) -> SmokeTestSuite:
        SmokeTestSuite(tests: [], config: config)

    # Add smoke test
    fn test(name: text, func: fn() -> bool) -> SmokeTestSuite:
        self.tests.append(SmokeTest(name: name, func: func))
        self

    # Run all tests
    fn run() -> List<SmokeTestResult>:
        var results = []
        for test in self.tests:
            val result = run_with_retries(test, self.config)
            results.append(result)

            if result.is_fail() and self.config.fail_fast:
                break

        results

    # Check if all passed
    fn all_passed(results: List<SmokeTestResult>) -> bool:
        results.all(\r: r.is_pass())

# Run single test with retries
fn run_with_retries(test: SmokeTest, config: SmokeTestConfig) -> SmokeTestResult:
    for attempt in 0..config.retry_attempts:
        val start = time.now_ms()

        try:
            val result = run_with_timeout(
                test.func,
                config.timeout_secs
            )

            val duration = time.now_ms() - start

            if result:
                return SmokeTestResult::Pass(
                    test_name: test.name,
                    duration_ms: duration
                )
        catch e:
            if attempt == config.retry_attempts - 1:
                return SmokeTestResult::Fail(
                    test_name: test.name,
                    error: e.to_string(),
                    attempt: attempt + 1
                )

        # Wait before retry
        time.sleep(config.retry_delay_secs)

    SmokeTestResult::Timeout(test_name: test.name)

# Canary deployment
class CanaryDeployment:
    app_name: text
    traffic_steps: List<i32>  # e.g., [5, 25, 50, 100]
    metrics: List<MetricCheck>
    step_duration_secs: f64

    static fn new(app_name: text) -> CanaryDeployment:
        CanaryDeployment(
            app_name: app_name,
            traffic_steps: [5, 25, 50, 100],
            metrics: [],
            step_duration_secs: 300.0  # 5 minutes
        )

    fn with_traffic_steps(steps: List<i32>) -> CanaryDeployment:
        self.traffic_steps = steps
        self

    fn check_metric(name: text, threshold: fn(f64) -> bool) -> CanaryDeployment:
        self.metrics.append(MetricCheck(name: name, threshold: threshold))
        self

    # Run canary deployment
    fn deploy(new_version: text) -> CanaryResult:
        for step in self.traffic_steps:
            print "Shifting {step}% traffic to {new_version}..."

            # Update traffic split (platform-specific)
            set_traffic_weight(self.app_name, new_version, step)

            # Wait for metrics to stabilize
            time.sleep(self.step_duration_secs)

            # Check metrics
            for metric in self.metrics:
                val value = get_metric_value(metric.name)
                if not metric.threshold(value):
                    print "❌ Metric {metric.name} failed: {value}"
                    rollback(self.app_name)
                    return CanaryResult::Failed(
                        step: step,
                        metric: metric.name,
                        value: value
                    )

            print "✅ Step {step}% passed"

        CanaryResult::Success(version: new_version)

# Blue-Green deployment
class BlueGreenDeployment:
    app_name: text
    blue_url: text
    green_url: text

    fn deploy_to_green(version: text):
        """Deploy new version to green environment."""
        # Platform-specific deployment
        deploy(self.green_url, version)

    fn run_smoke_tests(url: text) -> bool:
        """Run smoke tests against environment."""
        val suite = SmokeTestSuite.new()
            .test("homepage", \: http.get("{url}/").status == 200)
            .test("health", \: http.get("{url}/health").status == 200)

        val results = suite.run()
        suite.all_passed(results)

    fn switch_traffic():
        """Switch traffic from blue to green."""
        # Update load balancer/router
        update_router(self.app_name, target: self.green_url)

    fn rollback():
        """Switch traffic back to blue."""
        update_router(self.app_name, target: self.blue_url)

    # Full deployment workflow
    fn deploy(version: text) -> Result<(), text>:
        print "Deploying {version} to green..."
        self.deploy_to_green(version)

        print "Running smoke tests on green..."
        if not self.run_smoke_tests(self.green_url):
            return Err("Smoke tests failed on green")

        print "Switching traffic to green..."
        self.switch_traffic()

        print "Deployment complete. Blue available for rollback."
        Ok(())
```

#### Usage Examples

**Example 1: Smoke tests**
```simple
import std.testing.deployment

fn main():
    val suite = SmokeTestSuite.new()
        .test("homepage loads", \:
            http.get("https://myapp.com/").status == 200
        )
        .test("database connected", \:
            db.ping().is_ok()
        )
        .test("API health check", \:
            val resp = http.get("https://myapp.com/api/health")
            resp.status == 200 and resp.body["status"] == "ok"
        )
        .test("authentication works", \:
            val resp = http.post("https://myapp.com/login", {
                username: "test",
                password: "test123"
            })
            resp.status == 200
        )

    print "Running smoke tests..."
    val results = suite.run()

    for result in results:
        match result:
            Pass(name, duration):
                print "✅ {name} ({duration:.2f}ms)"
            Fail(name, error, attempt):
                print "❌ {name} failed after {attempt} attempts: {error}"
            Timeout(name):
                print "⏱️  {name} timed out"

    if suite.all_passed(results):
        print "\n✅ All smoke tests passed!"
        exit(0)
    else:
        print "\n❌ Some smoke tests failed!"
        exit(1)
```

**Example 2: Canary deployment**
```simple
import std.testing.deployment

fn main():
    val canary = CanaryDeployment.new("my-app")
        .with_traffic_steps([5, 10, 25, 50, 100])
        .check_metric("error_rate", \rate: rate < 0.01)  # < 1% errors
        .check_metric("p99_latency_ms", \latency: latency < 500.0)  # < 500ms
        .check_metric("cpu_usage", \cpu: cpu < 0.8)  # < 80% CPU

    val result = canary.deploy("v2.0.0")

    match result:
        Success(version):
            print "✅ Canary deployment of {version} successful!"
        Failed(step, metric, value):
            print "❌ Canary failed at {step}% on metric {metric}: {value}"
            print "Rolled back to previous version."
```

**Example 3: Blue-green deployment**
```simple
import std.testing.deployment

fn main():
    val deployment = BlueGreenDeployment(
        app_name: "my-app",
        blue_url: "https://blue.myapp.com",
        green_url: "https://green.myapp.com"
    )

    match deployment.deploy("v2.0.0"):
        Ok(_):
            print "✅ Blue-green deployment successful!"
            print "Green is now live. Blue available for rollback."
        Err(error):
            print "❌ Deployment failed: {error}"
            print "Traffic remains on blue."
```

### 6.6 Implementation Plan

**Phase 1: Smoke tests (1 week)**
- [ ] Implement `SmokeTestSuite` and `SmokeTest`
- [ ] Add retry logic with configurable delays
- [ ] Implement timeout support
- [ ] Add result reporting
- [ ] Write unit tests

**Phase 2: CLI integration (3 days)**
- [ ] Add `simple smoke` command
- [ ] Load tests from config file
- [ ] Generate JSON/HTML reports
- [ ] Exit with error code on failure

**Phase 3: Canary deployment (1 week)**
- [ ] Implement `CanaryDeployment`
- [ ] Add metric checking interface
- [ ] Integrate with Prometheus/CloudWatch
- [ ] Add rollback logic
- [ ] Test with Kubernetes

**Phase 4: Blue-green deployment (1 week)**
- [ ] Implement `BlueGreenDeployment`
- [ ] Add router/load balancer integrations
- [ ] Implement traffic switching
- [ ] Add rollback automation

**Phase 5: Advanced features (1 week, optional)**
- [ ] Add A/B testing support
- [ ] Implement shadow traffic (dark launch)
- [ ] Add deployment notifications (Slack, email)
- [ ] Generate deployment reports

### 6.7 Recommendations

**Priority: MEDIUM**

🟡 **Implement** smoke testing (Phase 1-2)

**Rationale:**
- Useful for compiler releases and stdlib deployments
- Relatively simple to implement (~400 LOC)
- High value for CI/CD pipelines
- Can reuse existing HTTP client

⏸️ **Defer** canary/blue-green (Phase 3-4)

**Rationale:**
- Platform-specific (K8s, AWS, etc.)
- Complex integration requirements
- Can use external tools (Flagger, Harness) for now

---

## 7. Summary & Recommendations

### 7.1 Implementation Priority

| Feature | Status | Priority | Effort | ROI | Recommendation |
|---------|--------|----------|--------|-----|----------------|
| **Property-Based Testing** | ✅ Done | N/A | - | - | Use existing |
| **Snapshot Testing** | ✅ Done | N/A | - | - | Use existing |
| **Benchmarking** | 🟡 Partial | **HIGH** | 2 weeks | High | **Implement stdlib** |
| **Smoke Tests** | ❌ None | **MEDIUM** | 1 week | High | **Implement** |
| **Mock Library** | ❌ None | **MEDIUM** | 3 weeks | Medium | Implement (blocked) |
| **Contract Testing** | ❌ None | **LOW** | 5 weeks | Low | Defer |
| **Canary/Blue-Green** | ❌ None | **LOW** | 2 weeks | Medium | Defer |

### 7.2 Recommended Roadmap

**Quarter 1: Core Testing (Weeks 1-4)**
1. Week 1-2: Implement `std.testing.benchmark`
2. Week 3: Implement `std.testing.deployment` (smoke tests only)
3. Week 4: Documentation and examples

**Quarter 2: Advanced Testing (Weeks 5-8)**
4. Week 5-7: Implement `std.testing.mock` (if trait objects ready)
5. Week 8: Integration with CI/CD

**Quarter 3+: Optional (Deferred)**
6. Contract testing (if building microservices)
7. Canary/blue-green (if deploying to K8s/cloud)

### 7.3 Quick Wins (Do Now)

✅ **Benchmarking library** - High impact, moderate effort
✅ **Smoke tests** - Essential for releases, easy to implement

### 7.4 Blocked (Wait For Infrastructure)

⏸️ **Mock library** - Needs trait objects and `any` type
⏸️ **Contract testing** - Needs HTTP server infrastructure

### 7.5 Low Priority (Use External Tools)

🔽 **Canary/blue-green** - Use Flagger, Harness, or Spinnaker
🔽 **Contract testing** - Use Pact libraries from other languages

---

## 8. Sources

### Property-Based Testing
- [Martin Fowler - Test Double](https://martinfowler.com/bliki/TestDouble.html)
- [QuickCheck Paper](https://www.cs.tufts.edu/~nr/cs257/archive/john-hughes/quick.pdf)

### Snapshot Testing
- [Jest Snapshot Testing](https://jestjs.io/docs/snapshot-testing)
- [insta (Rust) Documentation](https://yossarian.net/til/post/snapshot-testing-with-insta/)
- [Pytest Regressions (2025)](https://johal.in/pytest-regressions-data-golden-file-updates-2025/)
- [Playwright Visual Comparisons](https://playwright.dev/docs/test-snapshots)
- [Snapshot Testing Benefits and Drawbacks](https://www.sitepen.com/blog/snapshot-testing-benefits-and-drawbacks)

### Benchmarking
- [hyperfine GitHub](https://github.com/sharkdp/hyperfine)
- [Benchmarking - The Rust Performance Book](https://nnethercote.github.io/perf-book/benchmarking.html)
- [How to Benchmark Python Code](https://switowski.com/blog/how-to-benchmark-python-code/)
- [How to Benchmark with hyperfine](https://notes.suhaib.in/docs/tech/utilities/how-to-benchmark-anything-with-time-hyperfine-and-more/)

### Mock Libraries
- [Martin Fowler - Mocks Aren't Stubs](https://martinfowler.com/articles/mocksArentStubs.html)
- [Mock, Stub, Spy and Test Doubles](https://medium.com/@matiasglessi/mock-stub-spy-and-other-test-doubles-a1869265ac47)
- [Stubs vs Mocks vs Fakes vs Spy](https://www.ankursheel.com/blog/difference-stubs-mocks-fakes-spies)
- [Unit Testing: Test Doubles - Microsoft](https://learn.microsoft.com/en-us/archive/msdn-magazine/2007/september/unit-testing-exploring-the-continuum-of-test-doubles)

### Contract Testing
- [Pact Documentation](https://docs.pact.io/)
- [Consumer-Driven Contract Testing - Microsoft](https://microsoft.github.io/code-with-engineering-playbook/automated-testing/cdc-testing/)
- [What is CDC? - Pactflow](https://pactflow.io/what-is-consumer-driven-contract-testing/)
- [PACT Contract Testing Guide](https://www.hypertest.co/contract-testing/pact-contract-testing/)
- [Consumer Driven Contracts with Pact - Baeldung](https://www.baeldung.com/pact-junit-consumer-driven-contracts)

### Deployment Verification
- [Blue-Green Deployments - Christian Posta](https://blog.christianposta.com/deploy/blue-green-deployments-a-b-testing-and-canary-releases/)
- [Blue-Green vs Smoke Testing - Unleash](https://www.getunleash.io/blog/blue-green-deployment-vs-smoke-test)
- [Canary vs Smoke Testing - Unleash](https://www.getunleash.io/blog/canary-release-vs-smoke-test)
- [Blue-Green vs Canary - Codefresh](https://codefresh.io/learn/software-deployment/blue-green-deployment-vs-canary-5-key-differences-and-how-to-choose/)
- [Flagger - Blue/Green Deployments](https://docs.flagger.app/tutorials/kubernetes-blue-green)

---

**Document Status:** Complete - Ready for review and prioritization
**Next Steps:** Review with team, prioritize implementation, allocate resources
