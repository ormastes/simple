# Test Result and Timing Database Research

**Date:** 2026-01-21
**Status:** Research Complete
**Target:** Unified test result database with execution status and timing records

## Executive Summary

This research investigates best practices for managing test execution data in textual databases, combining test results (pass/fail status) with timing analysis. The focus is on handling timing variance (the "most high problem" since timing changes often). The goal is to design a robust unified system for:

1. **Test Database:** Track test execution status (pass/fail) with timing records
2. **Bug Database:** Link bugs to reproducible test cases
3. **Timing Management:** Handle variance with statistical methods and configurable thresholds
4. **Unified Reporting:** Single document showing test results + timing analysis

## Problem Statement

### Core Challenge

Test execution times are highly variable due to:
- System load fluctuations
- I/O operations
- Network latency
- GC pauses
- Background processes

**Issue:** Storing every timing update creates noise and makes it hard to detect real performance regressions.

**Goal:** Update timing data only when statistically significant changes occur.

## Research Findings

### 1. Best Practices from Industry

#### Netflix Performance Regression Detection

**Source:** [Fixing Performance Regressions Before They Happen](https://netflixtechblog.com/fixing-performance-regressions-before-they-happen-eab2602b86fe)

**Method:**
- Track last 40 runs
- Alert when new timing > mean + 4×std_dev
- Automated detection in CI/CD

**Key Insight:** Use historical window (40 runs) rather than single baseline.

#### Bencher Continuous Benchmarking

**Sources:**
- [Thresholds & Alerts](https://bencher.dev/docs/explanation/thresholds/)
- [How to Track Benchmarks in CI](https://bencher.dev/docs/how-to/track-benchmarks/)
- [What is Continuous Benchmarking?](https://bencher.dev/docs/explanation/continuous-benchmarking/)

**Features:**
- Student's t-test for regression detection
- Configurable upper/lower boundaries (e.g., 0.99 for 99th percentile)
- Sample size limits (e.g., max 64 samples)
- Percentage-based thresholds (e.g., ±10% from mean)
- Time windows for metrics (e.g., 4-week rolling window)

**Key Insight:** Multiple statistical methods available; t-test catches subtle regressions.

#### pytest-benchmark

**Sources:**
- [pytest-benchmark PyPI](https://pypi.org/project/pytest-benchmark/)
- [pytest-benchmark documentation](https://pytest-benchmark.readthedocs.io/)
- [Comparing past runs](https://pytest-benchmark.readthedocs.io/en/latest/comparing.html/)

**Data Collected:**
- `min`, `max`, `mean` - Basic statistics
- `median` - Robust central tendency
- `stddev` - Variance measure
- `iqr` - Interquartile range (25th-75th percentile)
- `outliers` - Count of statistical outliers
- `ops` - Operations per second
- `rounds`, `iterations` - Sample metadata

**Storage:** JSON format with names like `0001_foobar.json`

**Key Insight:** Store both mean (all data) and median (outlier-resistant).

#### Visual Studio Load Test Results Database

**Sources:**
- [Dissecting VS Load Test DB Schema (Microsoft Learn)](https://learn.microsoft.com/en-us/archive/blogs/geoffgr/dissecting-the-visual-studio-load-test-results-database-part-1intro-to-the-schema)
- [VS Load Test DB Schema (Developer Support)](https://devblogs.microsoft.com/premier-developer/dissecting-the-visual-studio-load-test-results-database-part-1intro-to-the-schema/)

**Schema Fields:**
- `Qty` - Sample count
- `Min`, `Max`, `Avg`, `Mean` - Central tendency
- `Std Dev` - Variance
- `90%`, `95%`, `99%` - Percentiles for SLA tracking
- `LoadTestRunId` - Links to specific test run

**Key Insight:** Percentiles (90%, 95%, 99%) critical for SLA compliance.

### 2. Statistical Methods for Timing Variance

#### Coefficient of Variation (CV%)

**Source:** [Statistical Methods for Reliable Benchmarks](https://modulovalue.com/blog/statistical-methods-for-reliable-benchmarks/)

**Formula:** `CV% = (std_dev / mean) × 100`

**Interpretation:**
- CV% < 20%: Reliable, low variance
- CV% 20-50%: Moderate variance, acceptable
- CV% > 50%: Unreliable, high variance

**Use Case:** Identify which tests have unstable timing (top 5% CV%).

**Key Insight:** CV% normalizes variance, allowing comparison across tests with different magnitudes.

#### Outlier Detection Methods

**Sources:**
- [Outlier Detection: Z-score, IQR, MAD](https://medium.com/@aakash013/outlier-detection-treatment-z-score-iqr-and-robust-methods-398c99450ff3)
- [NASA Robust Statistical Methods](https://ntrs.nasa.gov/api/citations/19880003299/downloads/19880003299.pdf)
- [Complete Guide to IQR Method](https://plotnerd.com/blog/complete-guide-to-iqr-method-outlier-detection/)
- [MAD for Response Time Analysis](https://www.frontiersin.org/journals/psychology/articles/10.3389/fpsyg.2021.675558/full)

**1. IQR (Interquartile Range) Method**

```
Q1 = 25th percentile
Q3 = 75th percentile
IQR = Q3 - Q1
Lower bound = Q1 - 1.5×IQR
Upper bound = Q3 + 1.5×IQR
```

**Advantages:**
- Robust to outliers (ignores extreme values)
- Works for any distribution shape
- Simple to implement

**Use Case:** Filter outliers before computing mean/std_dev.

**2. MAD (Median Absolute Deviation) Method**

```
MAD = median(|x_i - median(x)|)
Modified Z-score = 0.6745 × (x_i - median) / MAD
Outlier if |modified Z-score| > 3.5
```

**Advantages:**
- More robust than IQR
- Recommended for response time analysis
- Resistant to extreme outliers

**Use Case:** Detect anomalous test runs before updating baseline.

**3. Z-Score Method**

```
Z-score = (x - mean) / std_dev
Outlier if |Z-score| > 3 (or 2.5 for stricter)
```

**Disadvantages:**
- Sensitive to outliers (uses mean/std_dev)
- Assumes normal distribution

**Use Case:** When data is known to be normally distributed.

#### Robust Central Tendency

**Recommendation:** Use **median** instead of **mean** for baseline.

**Rationale:**
- Median ignores outliers
- Mean is skewed by extreme values
- Test timing often has right-skewed distribution (occasional slow runs)

**Key Insight:** Store both mean (for completeness) and median (for decisions).

### 3. Baseline Update Strategies

**Sources:**
- [Baseline Testing Best Practices](https://www.virtuosoqa.com/post/baseline-testing)
- [BlazeMeter Baseline Comparison](https://help.blazemeter.com/docs/guide/performance-baseline-comparison.html)
- [Performance Baseline Tests to Enforce SLAs](https://www.blazemeter.com/blog/performance-baseline-tests)
- [Establishing baseline metrics for A/B testing](https://www.statsig.com/perspectives/baseline-metrics-ab-test)
- [Database schema changes with no downtime](https://www.cockroachlabs.com/blog/how-to-update-database-schema/)

#### When to Update Baselines

**1. Scheduled Reviews**
- Quarterly reviews (minimum)
- After major releases
- When business requirements change

**Rationale:** Baselines become stale; products/users/markets change.

**2. Statistical Triggers**

**User's Requirements:**
- Default: Update only when running **all tests**
- Record avg time, update when **5% change** occurs
- Record std_dev, update when **>10% variation** exists
- Record only **top 5% in std_dev** (highest variance tests)
- Option to rewrite top 5% std_dev points

**Industry Standards:**
- Update when CV% drops below threshold (test stabilized)
- Update after N consecutive runs within tolerance
- Update when environment changes (hardware upgrade, OS update)

**3. Approval-Based Updates**

**Manual Review:**
- Team reviews flagged deviations
- Determines if changes are intentional
- Approves baseline update

**Automated with Gates:**
- Auto-update if change appears in multiple environments
- Requires CI/CD approval gate
- Version-controlled baselines (merge with code)

**Key Insight:** Combine statistical triggers with human approval for critical tests.

### 4. Rolling Window Statistics

**Sources:**
- [Moving average - Wikipedia](https://en.wikipedia.org/wiki/Moving_average)
- [Exponential smoothing - Wikipedia](https://en.wikipedia.org/wiki/Exponential_smoothing)
- [Rolling Windows & Moving Averages](https://sawdatascience.com/rolling-windows-moving-averages/)
- [Exponential Moving Average - Lei Mao's Log Book](https://leimao.github.io/blog/Exponential-Moving-Average/)

#### Simple Moving Average (SMA)

```
SMA_n = (x_1 + x_2 + ... + x_n) / n
```

**Use Case:** Track average over last N runs (e.g., N=40 like Netflix).

**Advantages:**
- Simple to implement
- Equal weight to all samples in window

**Disadvantages:**
- Older samples have same weight as recent
- Requires storing all N samples

#### Exponential Moving Average (EMA)

```
EMA_t = α × x_t + (1-α) × EMA_{t-1}
where α = smoothing factor (e.g., 0.2)
```

**Use Case:** Weight recent runs more heavily.

**Advantages:**
- Only stores single value (EMA_{t-1})
- More responsive to recent changes
- Memory efficient

**Disadvantages:**
- Less intuitive than SMA
- Requires tuning α parameter

**Key Insight:** EMA for real-time dashboards, SMA for historical analysis.

### 5. Configurable Thresholds

**Sources:**
- [Bencher Thresholds & Alerts](https://bencher.dev/docs/explanation/thresholds/)
- [BlazeMeter Failure Criteria](https://help.blazemeter.com/docs/guide/performance-failure-criteria.html)
- [Azure Performance Testing Strategies](https://learn.microsoft.com/en-us/azure/well-architected/performance-efficiency/performance-test)

#### Threshold Types

**1. Percentage-Based**
```
alert if: new_time > baseline × (1 + threshold_pct)
example: new_time > baseline × 1.05  # 5% threshold
```

**2. Standard Deviation-Based**
```
alert if: new_time > mean + k×std_dev
example: new_time > mean + 4×std_dev  # Netflix's method
```

**3. Percentile-Based**
```
alert if: new_time > 95th_percentile
```

**4. Absolute Time-Based**
```
alert if: new_time > max_allowed_ms
example: new_time > 1000ms  # SLA requirement
```

#### Configuration Recommendations

**Per-Test Configuration:**
```sdn
{
  test_id: "test_foo_performance"
  timing_config: {
    update_threshold_pct: 5.0        # Update baseline if 5% change
    alert_threshold_pct: 10.0        # Alert if 10% regression
    std_dev_threshold: 4.0           # Alert if >4 std_dev from mean
    min_sample_size: 10              # Require 10 runs before alerts
    max_sample_size: 40              # Rolling window of 40 runs
    use_median: true                 # Use median instead of mean
    outlier_method: "MAD"            # Use MAD for outlier detection
  }
}
```

**Global Defaults:**
```sdn
{
  default_timing_config: {
    update_threshold_pct: 5.0
    alert_threshold_pct: 10.0
    std_dev_threshold: 4.0
    min_sample_size: 10
    max_sample_size: 40
    use_median: true
    outlier_method: "IQR"
  }
}
```

**Key Insight:** Allow per-test overrides of global defaults.

## Database Schema Design

### Test Database Schema

```sdn
# test_db.sdn

{
  version: "1.0"
  last_updated: "2026-01-21T10:30:00Z"
  tests: [
    {
      # Identification
      test_id: "test_001"
      test_name: "core::net::http_client::test_get_request"
      test_file: "test/lib/std/unit/core/net/http_client_spec.spl"
      category: "network"

      # Execution Status
      status: "passed"  # passed, failed, skipped, ignored
      last_run: "2026-01-21T10:25:00Z"

      # Failure information (if status = failed)
      failure: {
        error_message: null      # Error message if test failed
        assertion_failed: null   # Which assertion failed
        location: null           # File:line where failure occurred
        stack_trace: null        # Stack trace if available
      }

      # Execution history (pass/fail over time)
      execution_history: {
        total_runs: 142
        passed: 140
        failed: 2
        last_10_runs: ["pass", "pass", "pass", "fail", "pass", "pass", "pass", "pass", "pass", "pass"]
        flaky: false             # True if intermittent failures
        failure_rate_pct: 1.4    # (failed / total_runs) × 100
      }

      # Timing Statistics (all in milliseconds)
      timing: {
        # Current baseline (used for comparisons)
        baseline_median: 45.2
        baseline_mean: 47.3
        baseline_std_dev: 12.1
        baseline_cv_pct: 25.6          # CV% = (std_dev/mean) × 100

        # Latest run
        last_run_time: 46.8

        # Historical window (last N runs)
        history: {
          window_size: 40              # Number of runs to track
          runs: [
            { timestamp: "2026-01-21T10:25:00Z", duration_ms: 46.8, outlier: false }
            { timestamp: "2026-01-21T09:15:00Z", duration_ms: 44.1, outlier: false }
            { timestamp: "2026-01-21T08:05:00Z", duration_ms: 125.3, outlier: true }
            # ... up to 40 entries
          ]
        }

        # Percentiles (for SLA tracking)
        p50: 45.2   # median
        p90: 68.5
        p95: 82.3
        p99: 105.7

        # Variance tracking
        min_time: 38.1
        max_time: 125.3
        iqr: 18.4                      # Q3 - Q1

        # Update metadata
        baseline_last_updated: "2026-01-15T14:20:00Z"
        baseline_run_count: 35         # Runs since last baseline update
        baseline_update_reason: "5% improvement detected"
      }

      # Timing configuration (overrides defaults)
      timing_config: {
        update_threshold_pct: 5.0
        alert_threshold_pct: 10.0
        std_dev_threshold: 4.0
        min_sample_size: 10
        max_sample_size: 40
        use_median: true
        outlier_method: "MAD"
      }

      # Links to bugs
      related_bugs: ["bug_042", "bug_137"]

      # Metadata
      tags: ["network", "http", "integration"]
      description: "Tests HTTP GET request with query parameters"
    }
  ]

  # Global configuration
  config: {
    default_timing_config: {
      update_threshold_pct: 5.0
      alert_threshold_pct: 10.0
      std_dev_threshold: 4.0
      min_sample_size: 10
      max_sample_size: 40
      use_median: true
      outlier_method: "IQR"
    }

    # Update rules
    update_rules: {
      update_on_all_tests_run: true    # User's requirement: default update only when running all tests
      track_top_variance_pct: 5.0      # User's requirement: record only top 5% in std_dev
      rewrite_top_variance: false      # User's requirement: option to rewrite top 5% std_dev points
    }
  }
}
```

### Bug Database Schema

```sdn
# bug_db.sdn

{
  version: "1.0"
  last_updated: "2026-01-21T10:30:00Z"
  bugs: [
    {
      # Identification
      bug_id: "bug_042"
      title: "HTTP client crashes on malformed response"

      # Status
      status: "open"  # open, in_progress, fixed, closed, wontfix
      priority: "P1"  # P0-P3
      severity: "critical"  # critical, major, minor, trivial

      # Description
      description: "When server returns malformed chunked encoding, client panics instead of returning error."

      # Reproducibility (REQUIRED)
      reproducible_by: ["test_001", "test_045"]  # MUST link to test cases
      reproduction_steps: "
        1. Run test_001 with malformed_response fixture
        2. Observe panic in http_client.spl:234
      "

      # Timing impact (optional)
      timing_impact: {
        affected_tests: ["test_001"]
        regression_pct: 150.0          # 150% slower when bug occurs
        intermittent: true             # Bug doesn't always trigger
      }

      # Links
      related_tests: ["test_001", "test_045", "test_067"]
      related_bugs: ["bug_137"]        # Duplicate or related

      # Metadata
      created: "2026-01-15T10:00:00Z"
      updated: "2026-01-21T09:30:00Z"
      assignee: "developer_name"
      reporter: "tester_name"
      tags: ["network", "http", "crash"]

      # Resolution (when status = fixed/closed)
      resolution: {
        fixed_in_commit: "abc123def456"
        verified_by: ["test_001", "test_045"]
        fixed_date: "2026-01-20T16:45:00Z"
      }
    }
  ]
}
```

### Generated Document: `doc/test/test_result.md`

This document combines test execution results with timing analysis in a single unified report.

```markdown
# Test Results

**Generated:** 2026-01-21 10:30:00
**Total Tests:** 234
**Status:** ⚠️ 3 FAILED

## Summary

| Status | Count | Percentage |
|--------|-------|------------|
| ✅ Passed | 231 | 98.7% |
| ❌ Failed | 3 | 1.3% |
| ⏭️ Skipped | 0 | 0.0% |
| 🔕 Ignored | 0 | 0.0% |

**Compared to previous run:** 🔴 +2 failures

---

## ❌ Failed Tests (3)

### 🔴 test_http_client_malformed_response

**File:** `test/lib/std/unit/core/net/http_client_spec.spl`
**Category:** network
**Failed:** 2026-01-21 10:25:00
**Flaky:** No (0% failure rate, first failure)

**Error:**
```
Assertion failed: expected Ok(_), got Err("panic: index out of bounds")
Location: http_client_spec.spl:145
```

**Linked Bugs:** [bug_042]

**Timing:** 67.3ms (baseline: 45.2ms, +48.9% 🔴)

---

### 🔴 test_gc_concurrent_allocation

**File:** `test/lib/std/unit/runtime/gc_spec.spl`
**Category:** runtime
**Failed:** 2026-01-21 10:26:15
**Flaky:** Yes (12% failure rate over 50 runs)

**Error:**
```
Assertion failed: memory corruption detected
Location: gc_spec.spl:234
Stack trace:
  at gc_spec.spl:234
  at gc.spl:678
  at runtime.spl:89
```

**Timing:** 234.5ms (baseline: 125.3ms, +87.1% 🔴)

---

### 🔴 test_type_inference_complex

**File:** `test/lib/std/unit/type/checker_spec.spl`
**Category:** type_system
**Failed:** 2026-01-21 10:27:30
**Flaky:** No (2% failure rate)

**Error:**
```
Assertion failed: type mismatch
Expected: i32
Got: u32
Location: checker_spec.spl:456
```

**Timing:** 12.4ms (baseline: 11.8ms, +5.1%)

---

## 📊 Timing Analysis

### Performance Regressions (2)

Tests that are significantly slower than baseline:

| Test | Current | Baseline | Change | Status |
|------|---------|----------|--------|--------|
| test_http_client_malformed_response | 67.3ms | 45.2ms | +48.9% | 🔴 ALERT |
| test_gc_concurrent_allocation | 234.5ms | 125.3ms | +87.1% | 🔴 ALERT |

### High Variance Tests (Top 5%)

Tests with unstable timing (CV% > 50%):

| Test | Mean | Std Dev | CV% | Recommendation |
|------|------|---------|-----|----------------|
| test_network_timeout | 125.3ms | 106.2ms | 84.7% | Investigate flakiness |
| test_gc_stress | 234.1ms | 168.9ms | 72.2% | May need longer warmup |
| test_concurrent_io | 89.4ms | 61.5ms | 68.8% | Check system load |

### Fastest Tests (Top 10)

| Test | Time |
|------|------|
| test_simple_addition | 0.3ms |
| test_variable_binding | 0.5ms |
| test_function_call | 0.8ms |
| ... | ... |

### Slowest Tests (Top 10)

| Test | Time |
|------|------|
| test_full_compilation | 2,345.6ms |
| test_large_file_parsing | 1,234.5ms |
| test_gc_stress | 234.1ms |
| ... | ... |

---

## 🎯 Action Items

### Priority 1: Fix Failing Tests (3)

1. **test_http_client_malformed_response** - Index out of bounds error
   - Related bug: bug_042
   - Timing regression: +48.9%

2. **test_gc_concurrent_allocation** - Memory corruption
   - Flaky test (12% failure rate)
   - Severe timing regression: +87.1%

3. **test_type_inference_complex** - Type mismatch
   - Reproducible failure
   - Minor timing impact: +5.1%

### Priority 2: Investigate Performance Regressions (2)

Tests showing significant slowdown compared to baseline:
- Investigate test_http_client_malformed_response (+48.9%)
- Investigate test_gc_concurrent_allocation (+87.1%)

### Priority 3: Stabilize Flaky Tests (1)

Tests with intermittent failures:
- test_gc_concurrent_allocation (12% failure rate)

---

## 📈 Trends (Last 10 Runs)

| Metric | Trend |
|--------|-------|
| Pass Rate | 98.3% → 98.7% → 98.7% 🟢 Stable |
| Failed Tests | 4 → 3 → 3 🟢 Improving |
| Avg Duration | 45.2ms → 46.1ms → 47.3ms 🟡 Slightly slower |
| Flaky Tests | 2 → 2 → 1 🟢 Improving |

---

**Previous Run:** 2026-01-21 09:30:00
**Changes:** +2 failures, +1 flaky test resolved
```

### Key Schema Design Decisions

**1. Test Database**
- **Execution Status:** Track pass/fail with error messages and failure history
- **Baseline:** Store both median (for decisions) and mean (for completeness)
- **History:** Rolling window of last N runs (default 40) for both timing and pass/fail
- **Percentiles:** Track 50th, 90th, 95th, 99th for SLA monitoring
- **Outliers:** Flag outliers in history, don't delete (for forensics)
- **Flakiness Detection:** Track failure rate and intermittent failures
- **Config:** Per-test overrides of global defaults

**2. Bug Database**
- **REQUIRED:** Every bug MUST link to reproducible test case(s)
- **Timing Impact:** Optional field to track performance regressions
- **Bidirectional Links:** Tests link to bugs, bugs link to tests

**3. Timing Update Rules**

**Condition 1: All Tests Run (User Requirement)**
```
IF all_tests_executed:
  THEN allow_baseline_update = true
ELSE:
  allow_baseline_update = false
```

**Condition 2: Significant Change (User Requirement)**
```
avg_change_pct = abs((new_median - baseline_median) / baseline_median) × 100
std_dev_change_pct = abs((new_std_dev - baseline_std_dev) / baseline_std_dev) × 100

IF avg_change_pct >= 5.0:           # User's 5% threshold
  update_baseline_median = true

IF std_dev_change_pct >= 10.0:      # User's 10% threshold
  update_baseline_std_dev = true
```

**Condition 3: Top Variance Tests (User Requirement)**
```
# Compute CV% for all tests
cv_pct_per_test = (std_dev / mean) × 100

# Sort by CV% descending
sorted_tests = sort_by(cv_pct_per_test, descending=true)

# Record only top 5%
top_5_pct_count = ceil(len(sorted_tests) × 0.05)
high_variance_tests = sorted_tests[0:top_5_pct_count]

# Option to rewrite top 5%
IF config.rewrite_top_variance:
  FOR test IN high_variance_tests:
    force_update_baseline(test)
```

## Update Algorithm

### Timing Update Logic

```rust
fn update_timing_baseline(
    test: &mut TestRecord,
    new_run: &TestRun,
    config: &TimingConfig,
    all_tests_run: bool,
) -> UpdateResult {
    // 1. Add new run to history
    test.timing.history.runs.push(new_run);

    // 2. Keep only last N runs (rolling window)
    if test.timing.history.runs.len() > config.max_sample_size {
        test.timing.history.runs.remove(0);
    }

    // 3. Detect outliers (before statistics)
    let outlier_free_runs = match config.outlier_method {
        OutlierMethod::IQR => detect_outliers_iqr(&test.timing.history.runs),
        OutlierMethod::MAD => detect_outliers_mad(&test.timing.history.runs),
        OutlierMethod::ZScore => detect_outliers_zscore(&test.timing.history.runs),
    };

    // 4. Compute statistics (on outlier-free data)
    let stats = compute_statistics(&outlier_free_runs);

    // 5. Check if baseline should update (user's requirements)

    // Requirement: Default update only when running all tests
    if !all_tests_run {
        test.timing.last_run_time = new_run.duration_ms;
        return UpdateResult::SkippedPartialRun;
    }

    // Requirement: Update avg time when 5% change
    let avg_change_pct = abs((stats.median - test.timing.baseline_median) / test.timing.baseline_median) * 100.0;
    let should_update_avg = avg_change_pct >= config.update_threshold_pct;

    // Requirement: Update std_dev when >10% variation
    let std_dev_change_pct = abs((stats.std_dev - test.timing.baseline_std_dev) / test.timing.baseline_std_dev) * 100.0;
    let should_update_std_dev = std_dev_change_pct >= 10.0;  // User's 10% threshold

    // 6. Update baseline if conditions met
    if should_update_avg || should_update_std_dev {
        if should_update_avg {
            test.timing.baseline_median = stats.median;
            test.timing.baseline_mean = stats.mean;
        }
        if should_update_std_dev {
            test.timing.baseline_std_dev = stats.std_dev;
            test.timing.baseline_cv_pct = (stats.std_dev / stats.mean) * 100.0;
        }

        test.timing.baseline_last_updated = now();
        test.timing.baseline_run_count = test.timing.history.runs.len();
        test.timing.baseline_update_reason = format!(
            "avg_change={:.1}%, std_dev_change={:.1}%",
            avg_change_pct, std_dev_change_pct
        );

        return UpdateResult::Updated;
    }

    // 7. No update, just record latest run
    test.timing.last_run_time = new_run.duration_ms;
    UpdateResult::NoUpdate
}
```

### Top Variance Tracking Logic

```rust
fn track_top_variance_tests(test_db: &mut TestDb, config: &GlobalConfig) -> Vec<String> {
    // 1. Compute CV% for all tests
    let mut cv_tests: Vec<(&str, f64)> = test_db.tests
        .iter()
        .map(|test| {
            let cv_pct = (test.timing.baseline_std_dev / test.timing.baseline_mean) * 100.0;
            (test.test_id.as_str(), cv_pct)
        })
        .collect();

    // 2. Sort by CV% descending
    cv_tests.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap());

    // 3. Get top 5% (user's requirement)
    let top_count = ((cv_tests.len() as f64) * (config.track_top_variance_pct / 100.0)).ceil() as usize;
    let top_variance_tests: Vec<String> = cv_tests[0..top_count]
        .iter()
        .map(|(id, _)| id.to_string())
        .collect();

    // 4. Option to rewrite top 5% (user's requirement)
    if config.rewrite_top_variance {
        for test_id in &top_variance_tests {
            if let Some(test) = test_db.tests.iter_mut().find(|t| t.test_id == *test_id) {
                // Force baseline update for high-variance tests
                let stats = compute_statistics(&test.timing.history.runs);
                test.timing.baseline_median = stats.median;
                test.timing.baseline_mean = stats.mean;
                test.timing.baseline_std_dev = stats.std_dev;
                test.timing.baseline_cv_pct = (stats.std_dev / stats.mean) * 100.0;
                test.timing.baseline_last_updated = now();
                test.timing.baseline_update_reason = format!("Top {}% variance rewrite", config.track_top_variance_pct);
            }
        }
    }

    top_variance_tests
}
```

## Implementation Recommendations

### 1. Database Storage

**Format:** SDN (Simple Data Notation) - already used in project
**Location:**
- `doc/test/test_db.sdn` - Test execution database
- `doc/bug/bug_db.sdn` - Bug tracking database

**Locking:** Use `FileLock` for atomic writes (already implemented in feature_db.rs)

### 2. Statistical Library

**Option A:** Implement in Rust (recommended)
```rust
// src/rust/driver/src/test_stats.rs
pub struct TimingStats {
    pub mean: f64,
    pub median: f64,
    pub std_dev: f64,
    pub cv_pct: f64,
    pub min: f64,
    pub max: f64,
    pub iqr: f64,
    pub p90: f64,
    pub p95: f64,
    pub p99: f64,
}

pub fn compute_statistics(samples: &[f64]) -> TimingStats { ... }
pub fn detect_outliers_iqr(samples: &[f64]) -> Vec<f64> { ... }
pub fn detect_outliers_mad(samples: &[f64]) -> Vec<f64> { ... }
```

**Option B:** Implement in Simple (for dogfooding)
```simple
# src/lib/std/src/stats/descriptive.spl
struct TimingStats:
    mean: f64
    median: f64
    std_dev: f64
    # ... other fields

fn compute_statistics(samples: [f64]) -> TimingStats:
    # Implementation
```

### 3. Configuration

**File:** `test_timing.sdn`
```sdn
{
  version: "1.0"

  # Global defaults
  default_timing_config: {
    update_threshold_pct: 5.0        # User's 5% requirement
    alert_threshold_pct: 10.0
    std_dev_threshold: 4.0
    min_sample_size: 10
    max_sample_size: 40
    use_median: true
    outlier_method: "MAD"            # IQR, MAD, or ZScore
  }

  # Update rules
  update_rules: {
    update_on_all_tests_run: true    # User's requirement
    track_top_variance_pct: 5.0      # User's 5% requirement
    rewrite_top_variance: false      # User's requirement (optional)
  }

  # Per-test overrides
  test_overrides: {
    "test_slow_network": {
      update_threshold_pct: 10.0     # More lenient for flaky test
      max_sample_size: 100           # More history for stability
    }
  }
}
```

### 4. Commands

**New CLI Commands:**
```bash
# Update test timing database after test run
simple test-timing-update <test_results.json>

# Generate timing report
simple test-timing-report [--top-variance] [--format=markdown]

# Rewrite top 5% variance baselines
simple test-timing-rewrite --top-variance-pct=5.0

# Validate timing configuration
simple test-timing-config --validate

# Export timing data
simple test-timing-export --format=json --output=timing_export.json
```

### 5. Integration with Test Runner

**Modify:** `src/rust/driver/src/cli/test_output.spl`

```simple
# After test execution
fn record_test_timing(test_id: str, duration_ms: f64, all_tests_run: bool):
    val db = load_test_db("doc/test/test_db.sdn")
    val test = db.find_test(test_id)

    val new_run = TestRun {
        timestamp: now()
        duration_ms: duration_ms
        outlier: false  # Will be determined later
    }

    val result = update_timing_baseline(test, new_run, test.timing_config, all_tests_run)

    match result:
        UpdateResult.Updated:
            print "Updated baseline for {test_id}"
        UpdateResult.NoUpdate:
            # Silent
        UpdateResult.SkippedPartialRun:
            # Silent

    save_test_db("doc/test/test_db.sdn", db)
```

### 6. Bug-Test Linking

**Enforce:** Every bug MUST have `reproducible_by` field

**Validation:**
```rust
// src/rust/driver/src/bug_db.rs
pub fn validate_bug_record(bug: &BugRecord, test_db: &TestDb) -> Result<(), String> {
    if bug.reproducible_by.is_empty() {
        return Err(format!("Bug {} has no reproducible test cases", bug.bug_id));
    }

    for test_id in &bug.reproducible_by {
        if !test_db.has_test(test_id) {
            return Err(format!("Bug {} references non-existent test {}", bug.bug_id, test_id));
        }
    }

    Ok(())
}
```

## Example Workflows

### Workflow 1: Run All Tests and Update Baselines

```bash
# Run full test suite
simple test --all

# Test runner automatically:
# 1. Records timing for each test
# 2. Detects outliers (MAD method)
# 3. Updates baselines if 5% avg change or 10% std_dev change
# 4. Writes to doc/test/test_db.sdn

# Generate report
simple test-timing-report --top-variance

# Output:
# Top 5% High Variance Tests:
# 1. test_network_timeout (CV% = 85.3%)
# 2. test_gc_stress (CV% = 72.1%)
# 3. test_concurrent_io (CV% = 68.9%)
```

### Workflow 2: Track Performance Regression

```bash
# Developer makes change
jj commit -m "Optimize HTTP client"

# CI runs tests
simple test --all

# Test runner detects regression:
# test_http_get: 45.2ms → 68.5ms (+51.5%)
# ALERT: Exceeds 10% threshold

# CI fails, reports:
# Performance Regression Detected:
# - test_http_get: +51.5% (baseline: 45.2ms, new: 68.5ms)
# - Threshold: 10%
# - Statistical significance: 5.2 std_dev above mean
```

### Workflow 3: Create Bug with Test Case

```bash
# Developer writes failing test
# test/lib/std/unit/core/net/http_client_bug_042_spec.spl

describe "Bug 042: Malformed response crash":
    it "should return error instead of panic":
        val client = HttpClient.new()
        val response = client.get("http://test.local/malformed")
        expect(response.is_err()).to_be(true)

# Run test (fails)
simple test test/lib/std/unit/core/net/http_client_bug_042_spec.spl

# Create bug record
simple bug-add \
  --id=bug_042 \
  --title="HTTP client crashes on malformed response" \
  --priority=P1 \
  --reproducible-by=test_http_client_bug_042

# Bug database validates:
# ✓ Bug bug_042 created
# ✓ Linked to test: test_http_client_bug_042
# ✓ Test exists and is currently FAILING
```

### Workflow 4: Rewrite High Variance Tests

```bash
# After major system upgrade (new hardware, OS, etc.)
# High variance tests need baseline reset

# Rewrite top 5% variance tests
simple test-timing-rewrite --top-variance-pct=5.0

# Output:
# Rewriting baselines for top 5% variance tests:
# 1. test_network_timeout (CV%: 85.3% → recalculated)
# 2. test_gc_stress (CV%: 72.1% → recalculated)
# 3. test_concurrent_io (CV%: 68.9% → recalculated)
#
# Baselines updated from last 40 runs
```

## Comparison with Existing Systems

### Simple's TODO System

**Current:**
- Manual: `simple todo-scan` (scans code)
- Auto-generates: `doc/TODO.md`
- Status: Manual annotation in code

**Proposed Test/Bug System:**
- Automatic: `simple test` (runs tests, records timing)
- Auto-generates: `doc/test/test_db.sdn`, `doc/bug/bug_db.sdn`
- Status: Auto-computed from test results

**Similarity:** Both use SDN format, auto-generation pattern.

### Simple's Feature System

**Current:**
- Automatic: `simple test` (generates feature_db.sdn)
- Generates: `doc/feature/*.md` including `pending_feature.md`
- Status: Auto-computed from test status

**Proposed Test/Bug System:**
- Automatic: `simple test` (generates test_db.sdn)
- Generates: `doc/test/timing_report.md`, `doc/bug/bug_report.md`
- Status: Auto-computed from test results + timing variance

**Similarity:** Same pattern as feature system (test run → database update → doc generation).

## Key Takeaways

### User Requirements Met

✅ **Default: Update timing only when running all tests**
- Implemented via `update_on_all_tests_run: true`

✅ **Record only top 5% in std_dev**
- Implemented via `track_top_variance_pct: 5.0`

✅ **Write std_dev value and update when >10% variation exists**
- Implemented via `std_dev_change_pct >= 10.0` check

✅ **Option to rewrite top 5% std_dev points**
- Implemented via `rewrite_top_variance: false` (configurable)

✅ **Record avg time and update when 5% change occurs**
- Implemented via `update_threshold_pct: 5.0`

✅ **All numbers are configurable**
- Implemented via SDN config file with global defaults + per-test overrides

✅ **Bug must have link to test case that reproduces it**
- Enforced via `reproducible_by` required field + validation

### Statistical Methods Recommended

**For Outlier Detection:** MAD (Median Absolute Deviation)
- Most robust for response time analysis
- Recommended by research (Frontiers in Psychology, 2021)

**For Central Tendency:** Median (not mean)
- Ignores outliers
- Better for right-skewed distributions (test timing)

**For Variance Measure:** CV% (Coefficient of Variation)
- Normalizes variance across different magnitude tests
- Easy interpretation (CV% < 20% is reliable)

**For Regression Detection:** Mean + k×std_dev (k=4)
- Netflix's proven method
- Catches subtle regressions
- Low false positive rate

### Database Design Principles

**1. Store History, Not Just Baseline**
- Keep last N runs (default 40)
- Enables trend analysis
- Supports rolling window statistics

**2. Store Both Mean and Median**
- Mean for completeness
- Median for decision-making

**3. Store Percentiles**
- 50th (median), 90th, 95th, 99th
- Critical for SLA monitoring

**4. Per-Test Configuration**
- Global defaults
- Per-test overrides
- Flexibility for special cases

**5. Bidirectional Links**
- Tests → Bugs
- Bugs → Tests
- Enables impact analysis

## Next Steps

### Phase 1: Statistical Library (Rust)
1. Implement `src/rust/driver/src/test_stats.rs`
2. Functions: `compute_statistics()`, `detect_outliers_mad()`, `detect_outliers_iqr()`
3. Unit tests with known datasets

### Phase 2: Database Schema
1. Create `doc/test/test_db.sdn` structure
2. Create `doc/bug/bug_db.sdn` structure
3. Implement `src/rust/driver/src/test_db.rs` (similar to `feature_db.rs`, `todo_db.rs`)
4. Implement `src/rust/driver/src/bug_db.rs`

### Phase 3: Test Runner Integration
1. Modify `src/rust/driver/src/cli/test_output.spl`
2. Record timing after each test
3. Update baseline when conditions met
4. Save to database

### Phase 4: CLI Commands
1. `simple test-timing-report`
2. `simple test-timing-rewrite`
3. `simple bug-add`
4. `simple bug-link`

### Phase 5: Documentation Generation
1. Generate `doc/test/test_result.md` (combined test results + timing analysis)
2. Generate `doc/bug/bug_report.md`
3. Update CLAUDE.md with auto-generated docs table

## References

### Performance Regression Detection
- [Netflix: Fixing Performance Regressions Before They Happen](https://netflixtechblog.com/fixing-performance-regressions-before-they-happen-eab2602b86fe)

### Continuous Benchmarking
- [Bencher - Continuous Benchmarking](https://bencher.dev/)
- [Bencher: Thresholds & Alerts](https://bencher.dev/docs/explanation/thresholds/)
- [Bencher: How to Track Benchmarks in CI](https://bencher.dev/docs/how-to/track-benchmarks/)
- [Bencher: What is Continuous Benchmarking?](https://bencher.dev/docs/explanation/continuous-benchmarking/)

### Benchmark Tools
- [pytest-benchmark PyPI](https://pypi.org/project/pytest-benchmark/)
- [pytest-benchmark documentation](https://pytest-benchmark.readthedocs.io/)
- [pytest-benchmark: Comparing past runs](https://pytest-benchmark.readthedocs.io/en/latest/comparing.html/)

### Database Schemas
- [Dissecting Visual Studio Load Test Results Database Schema (Microsoft Learn)](https://learn.microsoft.com/en-us/archive/blogs/geoffgr/dissecting-the-visual-studio-load-test-results-database-part-1intro-to-the-schema)
- [Dissecting Visual Studio Load Test Results Database Schema (Developer Support)](https://devblogs.microsoft.com/premier-developer/dissecting-the-visual-studio-load-test-results-database-part-1intro-to-the-schema/)

### Statistical Methods
- [Statistical Methods for Reliable Benchmarks](https://modulovalue.com/blog/statistical-methods-for-reliable-benchmarks/)
- [Outlier Detection: Z-score, IQR, MAD](https://medium.com/@aakash013/outlier-detection-treatment-z-score-iqr-and-robust-methods-398c99450ff3)
- [NASA: Robust Statistical Methods for Automated Outlier Detection](https://ntrs.nasa.gov/api/citations/19880003299/downloads/19880003299.pdf)
- [Complete Guide to IQR Method Outlier Detection](https://plotnerd.com/blog/complete-guide-to-iqr-method-outlier-detection/)
- [Frontiers in Psychology: Comparison of Response Time Outlier Exclusion Methods](https://www.frontiersin.org/journals/psychology/articles/10.3389/fpsyg.2021.675558/full)

### Baseline Testing
- [Baseline Testing Best Practices](https://www.virtuosoqa.com/post/baseline-testing)
- [BlazeMeter: Baseline Comparison](https://help.blazemeter.com/docs/guide/performance-baseline-comparison.html)
- [BlazeMeter: Performance Baseline Tests to Enforce SLAs](https://www.blazemeter.com/blog/performance-baseline-tests)
- [BlazeMeter: Failure Criteria](https://help.blazemeter.com/docs/guide/performance-failure-criteria.html)

### Time Series & Moving Averages
- [Moving average - Wikipedia](https://en.wikipedia.org/wiki/Moving_average)
- [Exponential smoothing - Wikipedia](https://en.wikipedia.org/wiki/Exponential_smoothing)
- [Rolling Windows & Moving Averages](https://sawdatascience.com/rolling-windows-moving-averages/)
- [Lei Mao: Exponential Moving Average](https://leimao.github.io/blog/Exponential-Moving-Average/)

### Other Resources
- [Statsig: Establishing baseline metrics for A/B testing](https://www.statsig.com/perspectives/baseline-metrics-ab-test)
- [CockroachDB: How to change database schema with no downtime](https://www.cockroachlabs.com/blog/how-to-update-database-schema/)
- [Azure: Performance Testing Strategies](https://learn.microsoft.com/en-us/azure/well-architected/performance-efficiency/performance-test)

---

**End of Research Document**
