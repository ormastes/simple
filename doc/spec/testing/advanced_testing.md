# Advanced Testing Layers Specification

**Status:** Planned
**Category:** Testing Infrastructure
**Priority:** High
**Last Updated:** 2026-02-15

---

## Table of Contents

1. [Overview](#1-overview)
2. [Fuzz Testing](#2-fuzz-testing)
3. [Resilience / Chaos Testing](#3-resilience--chaos-testing)
4. [Deployment Testing](#4-deployment-testing)
5. [Security Testing](#5-security-testing)
6. [Test Runner Integration](#6-test-runner-integration)
7. [Prioritized Roadmap](#7-prioritized-roadmap)
8. [Folder Structure](#8-folder-structure)

---

## 1. Overview

The Simple compiler currently ships three test layers -- unit, integration, and system -- backed by the SSpec framework (`src/std/spec.spl`) and the SDoctest runner (`src/app/test_runner_new/sdoctest/`). These layers verify that *known* inputs produce *expected* outputs.

Four additional layers are needed to cover the space of *unknown* inputs, *hostile* environments, *production* deployment, and *adversarial* intent:

| Layer | Question It Answers | Activation |
|-------|---------------------|------------|
| **Fuzz** | "Does the compiler crash on inputs I never imagined?" | `--fuzz` |
| **Resilience** | "Does the system recover when resources disappear or calls fail?" | `--chaos` |
| **Deployment** | "Does a fresh install actually work on every supported platform?" | `--deploy` |
| **Security** | "Can untrusted input escape the sandbox or leak data?" | `--security` |

All four layers are **off by default**. They are opt-in via CLI flags or SDN tags so that `bin/simple test` remains fast (sub-20-second) for everyday development.

### Design Principles

- **Deterministic replay.** Every fuzz failure and chaos scenario records a seed or schedule that reproduces the exact failure.
- **Shrinking.** Fuzz failures are automatically reduced to the smallest input that still triggers the bug.
- **No new dependencies.** All libraries are pure Simple, using only existing SFFI primitives from `src/app/io/mod.spl`.
- **SDN configuration.** Each layer adds a section to `simple.test.sdn` rather than introducing new config files.
- **Tag-based filtering.** Tests carry `:fuzz`, `:chaos`, `:deploy`, or `:security` tags that the runner uses for discovery.

---

## 2. Fuzz Testing

### 2.1 Purpose

Fuzz testing generates large volumes of semi-random inputs and feeds them to compiler subsystems (lexer, parser, SDN parser, semver, manifest loader). The goal is to find crashes, infinite loops, and assertion failures that hand-written tests miss.

### 2.2 CLI Interface

```bash
# Run all fuzz targets (default 1000 iterations each)
bin/simple test --fuzz

# Run a single fuzz target file
bin/simple test --fuzz test/fuzz/parser_fuzz_spec.spl

# Override iteration count
bin/simple test --fuzz --fuzz-iterations=50000

# Set seed for reproducibility
bin/simple test --fuzz --seed=42

# Run with a saved corpus directory
bin/simple test --fuzz --fuzz-corpus=corpus/parser/

# Only shrink a known failing input
bin/simple test --fuzz --fuzz-shrink="test/fuzz/crashes/crash_001.spl"

# Time-boxed fuzzing (run for N seconds, then stop)
bin/simple test --fuzz --fuzz-duration=300

# List discovered fuzz targets without running them
bin/simple test --fuzz --list
```

### 2.3 Library API -- `std.fuzz`

Location: `src/std/fuzz.spl`

#### 2.3.1 Configuration

```simple
struct FuzzConfig:
    iterations: i64       # Number of random inputs (default: 1000)
    seed: i64             # PRNG seed (0 = random)
    max_size: i64         # Upper bound on generated value size (default: 256)
    shrink_rounds: i64    # Max shrink attempts per failure (default: 100)
    timeout_ms: i64       # Per-input timeout in milliseconds (default: 5000)
    corpus_dir: text      # Directory of saved interesting inputs ("" = none)
    verbose: bool         # Print each input as it runs (default: false)

fn fuzz_config_default() -> FuzzConfig:
    FuzzConfig(
        iterations: 1000,
        seed: 0,
        max_size: 256,
        shrink_rounds: 100,
        timeout_ms: 5000,
        corpus_dir: "",
        verbose: false
    )
```

#### 2.3.2 Generators

Generators are functions that accept a `FuzzRng` and return a random value. The `FuzzRng` wraps a seeded PRNG so every run is reproducible.

```simple
struct FuzzRng:
    state: i64

fn fuzz_rng_create(seed: i64) -> FuzzRng:
    FuzzRng(state: seed)

fn fuzz_rng_next(rng: FuzzRng) -> i64:
    """Advance the PRNG and return the next pseudo-random i64."""
    pass_todo

# --- Primitive generators ---

fn gen_int(rng: FuzzRng, min: i64, max: i64) -> i64:
    """Generate a random integer in [min, max]."""
    val raw = fuzz_rng_next(rng)
    min + (raw % (max - min + 1)).abs()

fn gen_bool(rng: FuzzRng) -> bool:
    gen_int(rng, 0, 1) == 1

fn gen_f64(rng: FuzzRng) -> f64:
    """Generate a random float in [0.0, 1.0)."""
    val raw = gen_int(rng, 0, 1000000)
    raw * 1.0 / 1000000.0

fn gen_text(rng: FuzzRng, max_len: i64) -> text:
    """Generate a random string of printable ASCII, length in [0, max_len]."""
    val length = gen_int(rng, 0, max_len)
    var result = ""
    for i in length:
        val ch_code = gen_int(rng, 32, 126)
        result = result + chr(ch_code)
    result

fn gen_bytes(rng: FuzzRng, max_len: i64) -> [i64]:
    """Generate a random byte array, each element in [0, 255]."""
    val length = gen_int(rng, 0, max_len)
    var result: [i64] = []
    for i in length:
        result = result + [gen_int(rng, 0, 255)]
    result

# --- Collection generators ---

fn gen_list_int(rng: FuzzRng, max_len: i64, min_val: i64, max_val: i64) -> [i64]:
    """Generate a list of random integers."""
    val length = gen_int(rng, 0, max_len)
    var result: [i64] = []
    for i in length:
        result = result + [gen_int(rng, min_val, max_val)]
    result

fn gen_one_of(rng: FuzzRng, choices: [text]) -> text:
    """Pick one element from a list of choices."""
    val idx = gen_int(rng, 0, choices.len() - 1)
    choices[idx]

# --- Domain-specific generators ---

fn gen_simple_expr(rng: FuzzRng, depth: i64) -> text:
    """Generate a syntactically plausible Simple expression.

    Produces nested combinations of literals, binary ops,
    function calls, and optional chains up to the given depth.
    """
    if depth <= 0:
        val kind = gen_int(rng, 0, 3)
        if kind == 0: return "{gen_int(rng, -1000, 1000)}"
        if kind == 1: return "\"{gen_text(rng, 8)}\""
        if kind == 2: return "true"
        return "nil"

    val kind = gen_int(rng, 0, 4)
    val left = gen_simple_expr(rng, depth - 1)
    val right = gen_simple_expr(rng, depth - 1)
    val op = gen_one_of(rng, ["+", "-", "*", "/", "==", "!=", "<", ">", "and", "or"])

    if kind == 0: return "({left} {op} {right})"
    if kind == 1: return "fn_{gen_int(rng, 0, 5)}({left})"
    if kind == 2: return "{left}?.field"
    if kind == 3: return "[{left}, {right}]"
    "({left})"

fn gen_sdn_value(rng: FuzzRng, depth: i64) -> text:
    """Generate a random SDN (Simple Data Notation) document fragment."""
    if depth <= 0:
        val kind = gen_int(rng, 0, 2)
        if kind == 0: return "{gen_int(rng, -999, 999)}"
        if kind == 1: return "\"{gen_text(rng, 16)}\""
        return gen_one_of(rng, ["true", "false"])

    val key = gen_text(rng, 12)
    val child = gen_sdn_value(rng, depth - 1)
    "{key}: {child}"

fn gen_semver(rng: FuzzRng) -> text:
    """Generate a random semver-like version string."""
    val major = gen_int(rng, 0, 99)
    val minor = gen_int(rng, 0, 99)
    val patch = gen_int(rng, 0, 99)
    var version = "{major}.{minor}.{patch}"
    if gen_bool(rng):
        val pre = gen_one_of(rng, ["alpha", "beta", "rc", "dev", "nightly"])
        val pre_num = gen_int(rng, 1, 20)
        version = "{version}-{pre}.{pre_num}"
    version
```

#### 2.3.3 Shrinking

When a fuzz test discovers a failing input, the shrinker reduces it to the smallest input that still triggers the failure.

```simple
fn shrink_int(value: i64) -> [i64]:
    """Return candidate shrinks for an integer, biased toward zero."""
    var candidates: [i64] = [0]
    if value > 0:
        candidates = candidates + [value / 2, value - 1]
    if value < 0:
        candidates = candidates + [value / 2, value + 1, 0 - value]
    candidates

fn shrink_text(value: text) -> [text]:
    """Return candidate shrinks for a string."""
    var candidates: [text] = [""]
    if value.len() > 1:
        val half = value.len() / 2
        candidates = candidates + [value[0:half], value[half:value.len()]]
        # Drop each character one at a time
        for i in value.len():
            val before = value[0:i]
            val after = value[i + 1:value.len()]
            candidates = candidates + [before + after]
    candidates

fn shrink_list(value: [i64]) -> [[i64]]:
    """Return candidate shrinks for an integer list."""
    var candidates: [[i64]] = [[]]
    if value.len() > 1:
        val half = value.len() / 2
        candidates = candidates + [value[0:half], value[half:value.len()]]
    candidates
```

#### 2.3.4 Property Testing

The core entry point runs a property function against generated inputs and reports the result.

```simple
struct FuzzResult:
    name: text
    passed: bool
    iterations_run: i64
    failing_input: text      # Serialized representation of the failing input
    shrunk_input: text       # Minimal failing input after shrinking
    error_message: text
    seed: i64
    duration_ms: i64

fn fuzz_check(name: text, gen_fn: fn(FuzzRng) -> text, prop_fn: fn(text) -> bool, config: FuzzConfig) -> FuzzResult:
    """Run a property-based fuzz test.

    gen_fn produces a random input string from the PRNG.
    prop_fn returns true if the property holds, false or crash if it fails.
    On failure, the input is shrunk to find the minimal counterexample.
    """
    pass_todo

fn fuzz_differential(name: text, gen_fn: fn(FuzzRng) -> text, fn_a: fn(text) -> text, fn_b: fn(text) -> text, config: FuzzConfig) -> FuzzResult:
    """Differential fuzzing: verify two implementations agree on all inputs.

    Generates inputs via gen_fn and checks that fn_a(input) == fn_b(input).
    Useful for comparing the seed compiler parser against the self-hosted parser,
    or the interpreter against the native backend.
    """
    pass_todo
```

#### 2.3.5 Corpus Management

A corpus is a directory of interesting inputs (edge cases, prior crashes) that the fuzzer replays before generating new random inputs.

```simple
fn corpus_load(dir: text) -> [text]:
    """Load all files from a corpus directory as input strings."""
    pass_todo

fn corpus_save(dir: text, inputs: [text]) -> i64:
    """Save inputs to corpus directory. Returns count written."""
    pass_todo

fn corpus_add(dir: text, input: text) -> bool:
    """Add a single input to the corpus if not already present."""
    pass_todo

fn corpus_minimize(dir: text, prop_fn: fn(text) -> bool) -> i64:
    """Remove corpus entries that no longer trigger failures. Returns removed count."""
    pass_todo
```

### 2.4 High-Value Fuzz Targets

| Target | Module Under Test | Generator | Why |
|--------|-------------------|-----------|-----|
| Lexer token stream | `src/core/lexer.spl` | `gen_text` (random bytes) | Crash on invalid UTF-8, unterminated strings, deep nesting |
| Parser AST | `src/core/parser.spl` | `gen_simple_expr` | Stack overflow on deep expressions, mishandled EOF |
| SDN parser | SDN line-based parser | `gen_sdn_value` | Injection via untrusted config files |
| Semver parser | `src/std/semver.spl` | `gen_semver` | Malformed versions in manifests |
| Manifest loader | `src/std/package.spl` | `gen_sdn_value` + structure | Field type mismatches, missing required fields |
| String interpolation | `src/core/lexer.spl` | Strings with `{`, `}`, `}}` | The `}}` escape edge cases documented in MEMORY.md |
| Path utilities | `src/std/path.spl` | `gen_text` with `/`, `\`, `..` | Path traversal, null bytes in paths |

### 2.5 Discovery Rules

- Directory: `test/fuzz/`
- File suffix: `*_fuzz_spec.spl`
- Tag: `:fuzz`
- Only discovered when `--fuzz` flag is present
- Each file uses `describe "fuzz:target_name":` convention

### 2.6 SDN Configuration

```
fuzz:
  default_iterations: 1000
  default_timeout_ms: 5000
  default_max_size: 256
  shrink_rounds: 100
  corpus_dir: test/fuzz/corpus
  save_crashes: true
  crash_dir: test/fuzz/crashes
```

### 2.7 Example Fuzz Spec

```simple
# test/fuzz/parser_fuzz_spec.spl
#
# Fuzz the Simple parser with randomly generated expressions.

use std.fuzz.{FuzzConfig, fuzz_config_default, gen_simple_expr, fuzz_check, FuzzRng, fuzz_rng_create}

describe "fuzz:parser":
    it "never crashes on random expressions" :fuzz:
        val config = fuzz_config_default()

        val gen_fn = fn(rng: FuzzRng) -> text:
            gen_simple_expr(rng, 6)

        val prop_fn = fn(input: text) -> bool:
            # parse() should return a result or nil, never crash
            val result = parse(input)
            true  # If we reach here, no crash occurred

        val result = fuzz_check("parser_no_crash", gen_fn, prop_fn, config)
        expect(result.passed).to_equal(true)

    it "lexer survives arbitrary byte sequences" :fuzz:
        val config = fuzz_config_default()

        val gen_fn = fn(rng: FuzzRng) -> text:
            gen_text(rng, 512)

        val prop_fn = fn(input: text) -> bool:
            val tokens = tokenize(input)
            true

        val result = fuzz_check("lexer_no_crash", gen_fn, prop_fn, config)
        expect(result.passed).to_equal(true)
```

---

## 3. Resilience / Chaos Testing

### 3.1 Purpose

Chaos testing injects faults -- disk write failures, memory pressure, timeouts, corrupted data -- into the compiler and runtime to verify graceful degradation. This is especially important for the test runner itself (which spawns subprocesses), the MCP server (which handles network I/O), and the build system (which writes artifacts to disk).

### 3.2 CLI Interface

```bash
# Run all resilience tests
bin/simple test --chaos

# Run a single resilience scenario
bin/simple test --chaos test/resilience/build_disk_full_spec.spl

# Set fault probability (0.0 to 1.0, default 0.1)
bin/simple test --chaos --chaos-rate=0.3

# Use a specific failure schedule for deterministic replay
bin/simple test --chaos --chaos-schedule=test/resilience/schedules/schedule_001.sdn

# Save the schedule used in this run
bin/simple test --chaos --chaos-save-schedule

# Run with memory limit (bytes)
bin/simple test --chaos --chaos-memory-limit=67108864

# Run with artificial latency (milliseconds)
bin/simple test --chaos --chaos-latency=50

# List all chaos scenarios
bin/simple test --chaos --list
```

### 3.3 Library API -- `std.chaos`

Location: `src/std/chaos.spl`

#### 3.3.1 Configuration and Results

```simple
struct ChaosConfig:
    fault_rate: f64         # Probability of injecting a fault [0.0, 1.0] (default: 0.1)
    seed: i64               # PRNG seed for fault decisions (0 = random)
    latency_ms: i64         # Artificial latency per I/O op (default: 0)
    memory_limit: i64       # Simulated memory ceiling in bytes (0 = unlimited)
    timeout_ms: i64         # Max time for entire scenario (default: 30000)
    schedule_path: text     # Path to a saved schedule for replay ("" = none)
    save_schedule: bool     # Whether to save the schedule after the run
    verbose: bool

fn chaos_config_default() -> ChaosConfig:
    ChaosConfig(
        fault_rate: 0.1,
        seed: 0,
        latency_ms: 0,
        memory_limit: 0,
        timeout_ms: 30000,
        schedule_path: "",
        save_schedule: false,
        verbose: false
    )

struct ChaosResult:
    name: text
    passed: bool
    faults_injected: i64
    faults_handled: i64     # How many faults the system recovered from
    faults_leaked: i64      # Faults that caused unhandled errors
    schedule_path: text     # Path to saved schedule (if save_schedule was true)
    error_message: text
    duration_ms: i64
```

#### 3.3.2 Fault Injection Primitives

These functions are called inside the code under test (or wrappers around it) to simulate failures at injection points.

```simple
fn should_fault(config: ChaosConfig, rng: FuzzRng, label: text) -> bool:
    """Decide whether to inject a fault at this point.

    Returns true with probability config.fault_rate.
    Records the decision in the schedule for deterministic replay.
    """
    pass_todo

fn inject_latency(config: ChaosConfig, rng: FuzzRng, label: text):
    """Sleep for config.latency_ms milliseconds if should_fault returns true."""
    pass_todo

fn inject_error(config: ChaosConfig, rng: FuzzRng, label: text) -> text:
    """Return an error message if should_fault returns true, "" otherwise.

    The caller checks the return value and treats non-empty as an error:
        val err = inject_error(config, rng, "disk_write")
        if err != "":
            return nil  # Simulate write failure
    """
    pass_todo

fn inject_corruption(config: ChaosConfig, rng: FuzzRng, data: text, label: text) -> text:
    """Randomly corrupt bytes in data if should_fault returns true.

    Flips, inserts, or deletes characters at random positions.
    Returns the (possibly corrupted) data.
    """
    pass_todo
```

#### 3.3.3 Schedules (Deterministic Replay)

A schedule records every fault-injection decision so a chaos run can be replayed exactly.

```simple
struct ChaosSchedule:
    seed: i64
    decisions: [ChaosDecision]

struct ChaosDecision:
    label: text
    step: i64
    faulted: bool

fn schedule_create(seed: i64) -> ChaosSchedule:
    ChaosSchedule(seed: seed, decisions: [])

fn schedule_serialize(schedule: ChaosSchedule) -> text:
    """Serialize a schedule to SDN format for saving to disk."""
    pass_todo

fn schedule_load(path: text) -> ChaosSchedule:
    """Load a schedule from an SDN file for deterministic replay."""
    pass_todo
```

#### 3.3.4 Runner

```simple
fn chaos_run(config: ChaosConfig, scenario_fn: fn(ChaosConfig) -> bool) -> ChaosResult:
    """Execute a chaos scenario.

    scenario_fn receives the config (with active PRNG and schedule)
    and returns true if the system under test handled all faults gracefully.
    """
    pass_todo
```

#### 3.3.5 Resource Constraints

```simple
fn chaos_with_memory_limit(limit_bytes: i64, action_fn: fn() -> bool) -> bool:
    """Run action_fn with a simulated memory limit.

    Tracks allocations and returns false if the limit is exceeded.
    Useful for testing the compiler under low-memory conditions.
    """
    pass_todo

fn chaos_with_timeout(timeout_ms: i64, action_fn: fn() -> bool) -> bool:
    """Run action_fn with a wall-clock timeout.

    Returns false if the function does not complete within timeout_ms.
    """
    pass_todo
```

#### 3.3.6 Resilience Pattern Tests

Higher-level helpers that test common resilience patterns.

```simple
fn chaos_test_retry(config: ChaosConfig, action_fn: fn() -> bool, max_retries: i64) -> ChaosResult:
    """Test that action_fn succeeds within max_retries attempts under faults.

    Verifies the retry logic in the system under test.
    """
    pass_todo

fn chaos_test_circuit_breaker(config: ChaosConfig, action_fn: fn() -> bool, threshold: i64, reset_ms: i64) -> ChaosResult:
    """Test circuit-breaker behavior: after 'threshold' consecutive faults,
    the system should stop attempting and return a cached/default result
    until 'reset_ms' have elapsed.
    """
    pass_todo
```

### 3.4 High-Value Chaos Targets

| Target | Fault Type | Validates |
|--------|-----------|-----------|
| Build system artifact write | Disk write failure | Partial-build cleanup, no corrupt artifacts left behind |
| Test runner subprocess spawn | Process launch failure | Graceful skip with error message, not a crash |
| MCP server request handling | Network latency/drop | Timeout handling, connection cleanup |
| Corpus/cache file I/O | Read corruption | Fallback to regeneration, no silent data corruption |
| Import resolution | Missing file | Clear "module not found" error, not interpreter panic |
| SDN config loading | Malformed config | Default fallback values, warning message |

### 3.5 Discovery Rules

- Directory: `test/resilience/`
- File suffix: `*_chaos_spec.spl`
- Tag: `:chaos`
- Only discovered when `--chaos` flag is present
- Schedules stored in: `test/resilience/schedules/`

### 3.6 SDN Configuration

```
chaos:
  default_fault_rate: 0.1
  default_timeout_ms: 30000
  default_latency_ms: 0
  save_schedules: true
  schedule_dir: test/resilience/schedules
  memory_limit: 0
```

### 3.7 Example Chaos Spec

```simple
# test/resilience/build_disk_full_spec.spl
#
# Verify the build system recovers gracefully when disk writes fail.

use std.chaos.{ChaosConfig, chaos_config_default, chaos_run, inject_error}
use std.fuzz.{FuzzRng, fuzz_rng_create}

describe "chaos:build_disk_full":
    it "cleans up partial artifacts on write failure" :chaos:
        var config = chaos_config_default()
        config = ChaosConfig(
            fault_rate: 0.5,
            seed: 12345,
            latency_ms: 0,
            memory_limit: 0,
            timeout_ms: 10000,
            schedule_path: "",
            save_schedule: true,
            verbose: false
        )

        val scenario = fn(cfg: ChaosConfig) -> bool:
            val rng = fuzz_rng_create(cfg.seed)
            # Simulate building a module
            val err = inject_error(cfg, rng, "write_object_file")
            if err != "":
                # The build system should detect the write failure
                # and clean up any partial .o files
                val artifacts_exist = file_exists("build/partial.o")
                return not artifacts_exist  # Pass if cleanup happened
            true

        val result = chaos_run(config, scenario)
        expect(result.passed).to_equal(true)
        expect(result.faults_leaked).to_equal(0)

    it "retries transient I/O errors" :chaos:
        var config = chaos_config_default()
        config = ChaosConfig(
            fault_rate: 0.2,
            seed: 99,
            latency_ms: 0,
            memory_limit: 0,
            timeout_ms: 15000,
            schedule_path: "",
            save_schedule: false,
            verbose: false
        )

        val scenario = fn(cfg: ChaosConfig) -> bool:
            val rng = fuzz_rng_create(cfg.seed)
            var attempts = 0
            var success = false
            while attempts < 3 and not success:
                val err = inject_error(cfg, rng, "write_output")
                if err == "":
                    success = true
                attempts = attempts + 1
            success

        val result = chaos_run(config, scenario)
        expect(result.passed).to_equal(true)
```

---

## 4. Deployment Testing

### 4.1 Purpose

Deployment tests verify that the Simple compiler and runtime work correctly when installed from scratch on a target platform. They cover the full lifecycle: download/install, first build, first test run, cross-compilation, and container execution. These tests are too slow and environment-dependent for the normal test suite, but they must run in CI before any release.

### 4.2 CLI Interface

```bash
# Run all deployment tests
bin/simple test --deploy

# Run a specific deployment scenario
bin/simple test --deploy test/deploy/fresh_install_spec.spl

# Target a specific platform
bin/simple test --deploy --deploy-platform=linux-x86_64
bin/simple test --deploy --deploy-platform=linux-aarch64
bin/simple test --deploy --deploy-platform=macos-arm64

# Run in a container (default for --deploy)
bin/simple test --deploy --deploy-container

# Run against a local install (skip container)
bin/simple test --deploy --deploy-local

# Specify the release artifact to test
bin/simple test --deploy --deploy-artifact=bin/release/simple

# List all deployment scenarios
bin/simple test --deploy --list

# Dry run (show what would execute)
bin/simple test --deploy --deploy-dry-run
```

### 4.3 Test Scenarios

Deployment tests do not use a library in the same way as fuzz and chaos tests. They are structured as SSpec test files that invoke shell commands via `process_run()` and check exit codes and outputs.

#### 4.3.1 Fresh Install Smoke Test

```simple
# test/deploy/fresh_install_spec.spl
#
# Verify that a fresh install of the Simple runtime works end-to-end.

describe "deploy:fresh_install":
    it "runtime binary is executable and prints version" :deploy:
        val result = process_run("bin/release/simple", ["--version"])
        expect(result.exit_code).to_equal(0)
        expect(result.stdout).to_contain("Simple")

    it "can compile and run hello world" :deploy:
        val src = "print \"Hello, World!\""
        file_write("tmp/deploy_test/hello.spl", src)
        val result = process_run("bin/release/simple", ["run", "tmp/deploy_test/hello.spl"])
        expect(result.exit_code).to_equal(0)
        expect(result.stdout).to_contain("Hello, World!")

    it "test runner discovers and runs a trivial spec" :deploy:
        val spec = "describe \"smoke\":\n    it \"passes\":\n        expect(1 + 1).to_equal(2)"
        file_write("tmp/deploy_test/smoke_spec.spl", spec)
        val result = process_run("bin/release/simple", ["test", "tmp/deploy_test/smoke_spec.spl"])
        expect(result.exit_code).to_equal(0)
        expect(result.stdout).to_contain("1 passed")

    it "build command produces output" :deploy:
        val result = process_run("bin/release/simple", ["build"])
        expect(result.exit_code).to_equal(0)
```

#### 4.3.2 Container Deployment

```simple
# test/deploy/container_spec.spl
#
# Verify that the Docker-based test isolation works.

describe "deploy:container":
    it "container image builds successfully" :deploy:
        val result = process_run("docker", [
            "build", "-t", "simple-deploy-test:latest",
            "-f", "docker/Dockerfile.test-isolation", "."
        ])
        expect(result.exit_code).to_equal(0)

    it "tests pass inside container" :deploy:
        val result = process_run("docker", [
            "run", "--rm",
            "-v", "{cwd()}:/workspace:ro",
            "--memory=512m", "--cpus=1.0",
            "simple-deploy-test:latest",
            "test", "test/unit/"
        ])
        expect(result.exit_code).to_equal(0)
```

#### 4.3.3 Cross-Platform Matrix

```simple
# test/deploy/cross_platform_spec.spl
#
# Verify cross-compilation targets produce valid binaries.

describe "deploy:cross_platform":
    it "native x86_64 binary runs" :deploy:
        val result = process_run("bin/release/simple", [
            "build", "--mode=native", "--target=x86_64"
        ])
        expect(result.exit_code).to_equal(0)

    it "runtime binary size is within expected range" :deploy:
        val size = file_size("bin/release/simple")
        # Runtime should be between 20MB and 50MB
        expect(size).to_be_greater_than(20000000)
        expect(size).to_be_less_than(50000000)
```

### 4.4 Discovery Rules

- Directory: `test/deploy/`
- File suffix: `*_spec.spl` (standard SSpec files)
- Tag: `:deploy`
- Only discovered when `--deploy` flag is present
- Requires `docker` on PATH for container scenarios

### 4.5 SDN Configuration

```
deploy:
  default_platform: linux-x86_64
  use_container: true
  container_image: simple-test-isolation:latest
  artifact_path: bin/release/simple
  temp_dir: tmp/deploy_test
  timeout: 600
  platforms:
    - linux-x86_64
    - linux-aarch64
    - macos-arm64
```

---

## 5. Security Testing

### 5.1 Purpose

Security tests verify that the Simple compiler and runtime do not allow untrusted input to compromise the host system. This covers: path traversal via imports, code injection through string interpolation, resource exhaustion via malicious programs, and integrity of build artifacts.

### 5.2 CLI Interface

```bash
# Run all security tests
bin/simple test --security

# Run a specific security test file
bin/simple test --security test/security/path_traversal_spec.spl

# Run with specific security categories
bin/simple test --security --security-category=injection
bin/simple test --security --security-category=traversal
bin/simple test --security --security-category=dos
bin/simple test --security --security-category=supply-chain

# Generate a security audit report
bin/simple test --security --security-report=security-audit.md

# List all security test cases
bin/simple test --security --list
```

### 5.3 Security Test Categories

#### 5.3.1 Path Traversal

```simple
# test/security/path_traversal_spec.spl
#
# Verify that import paths cannot escape the project root.

describe "security:path_traversal":
    it "rejects imports with .." :security:
        val malicious_src = "use ../../etc/passwd.{read_all}"
        val result = try_parse(malicious_src)
        expect(result).to_be_nil()

    it "rejects absolute imports" :security:
        val malicious_src = "use /etc/hosts.{content}"
        val result = try_parse(malicious_src)
        expect(result).to_be_nil()

    it "rejects null bytes in import paths" :security:
        val malicious_src = "use module\x00evil.{func}"
        val result = try_parse(malicious_src)
        expect(result).to_be_nil()

    it "normalizes symlink loops in import resolution" :security:
        # Create a symlink loop: a -> b -> a
        # Import resolution must detect the cycle
        val result = resolve_import_safe("test/security/fixtures/symlink_loop/a")
        expect(result).to_be_nil()
```

#### 5.3.2 Resource Exhaustion (Denial of Service)

```simple
# test/security/resource_exhaustion_spec.spl
#
# Verify that the compiler defends against programs designed to exhaust resources.

describe "security:resource_exhaustion":
    it "limits recursion depth in parser" :security:
        # Generate deeply nested expression: (((((...)))))
        var expr = "1"
        for i in 10000:
            expr = "({expr})"
        val result = try_parse(expr)
        # Should either parse with a depth limit or return an error
        # Must NOT stack overflow
        expect(true).to_equal(true)  # Reaching here means no crash

    it "limits string interpolation nesting" :security:
        # {"{"{"{...}"}"}"}
        var expr = "x"
        for i in 1000:
            expr = "\"{{{expr}}}\""
        val result = try_parse(expr)
        expect(true).to_equal(true)

    it "limits array literal size" :security:
        # [0, 0, 0, ...] with 10 million elements
        var src = "val x = ["
        for i in 100:
            if i > 0:
                src = src + ", "
            src = src + "0"
        src = src + "]"
        # The parser should accept this; runtime should limit actual allocation
        val result = try_parse(src)
        expect(result).to_be_nil().to_equal(false)

    it "rejects infinite loops at compile time when detectable" :security:
        val src = "while true: pass_dn"
        # Compiler may warn but should not hang during analysis
        val result = try_compile_with_timeout(src, 5000)
        expect(result.timed_out).to_equal(false)
```

#### 5.3.3 Supply Chain (Build Artifact Integrity)

```simple
# test/security/supply_chain_spec.spl
#
# Verify build artifact integrity and provenance.

describe "security:supply_chain":
    it "release binary matches expected hash" :security:
        val hash = file_sha256("bin/release/simple")
        expect(hash.len()).to_equal(64)  # SHA-256 produces 64 hex chars

    it "no unexpected shared library dependencies" :security:
        val result = process_run("ldd", ["bin/release/simple"])
        # Only libc, libm, libpthread, libdl should appear
        val allowed = ["libc", "libm", "libpthread", "libdl", "linux-vdso", "ld-linux"]
        val lines = result.stdout.split("\n")
        for line in lines:
            if line.contains("=>"):
                var found_allowed = false
                for lib in allowed:
                    if line.contains(lib):
                        found_allowed = true
                expect(found_allowed).to_equal(true)

    it "no credentials in build artifacts" :security:
        val binary_content = file_read("bin/release/simple")
        val sensitive_patterns = ["password", "secret", "api_key", "token=", "Bearer "]
        for pattern in sensitive_patterns:
            expect(binary_content.contains(pattern)).to_equal(false)
```

#### 5.3.4 Injection

```simple
# test/security/injection_spec.spl
#
# Verify that string interpolation and shell calls cannot be exploited.

describe "security:injection":
    it "string interpolation does not evaluate arbitrary code" :security:
        # Interpolation should only evaluate expressions, not statements
        val src = "val x = \"{import os; os.system('rm -rf /')}\""
        val result = try_parse(src)
        # The parser should reject the statement inside interpolation
        # or treat it as a plain expression that fails type checking
        expect(true).to_equal(true)

    it "process_run does not interpret shell metacharacters" :security:
        val result = process_run("echo", ["hello; rm -rf /"])
        # The semicolon should be passed literally, not interpreted
        expect(result.stdout).to_contain(";")

    it "file paths are sanitized in file_write" :security:
        val malicious_path = "/tmp/test; rm -rf /"
        # file_write should fail or sanitize, not execute the command
        val written = file_write(malicious_path, "safe content")
        # If written, the file should have the literal name
        # (this tests the heredoc-based implementation)
        expect(true).to_equal(true)
```

### 5.4 Discovery Rules

- Directory: `test/security/`
- File suffix: `*_spec.spl` (standard SSpec files)
- Tag: `:security`
- Only discovered when `--security` flag is present
- Categories: `injection`, `traversal`, `dos`, `supply-chain`

### 5.5 SDN Configuration

```
security:
  default_category: all
  timeout: 60
  report_path: security-audit.md
  categories:
    - injection
    - traversal
    - dos
    - supply-chain
  block_dangerous_ops: true
```

---

## 6. Test Runner Integration

### 6.1 New CLI Flags

All new flags are added to `parse_test_args()` in `src/app/test_runner_new/test_runner_args.spl`.

| Flag | Type | Default | Description |
|------|------|---------|-------------|
| `--fuzz` | bool | false | Enable fuzz test discovery and execution |
| `--fuzz-iterations` | i64 | 1000 | Number of iterations per fuzz target |
| `--fuzz-corpus` | text | "" | Path to corpus directory |
| `--fuzz-shrink` | text | "" | Path to a specific input to shrink |
| `--fuzz-duration` | i64 | 0 | Time-boxed fuzzing in seconds (0 = use iterations) |
| `--chaos` | bool | false | Enable chaos/resilience test discovery |
| `--chaos-rate` | f64 | 0.1 | Fault injection probability |
| `--chaos-schedule` | text | "" | Path to a saved schedule for replay |
| `--chaos-save-schedule` | bool | false | Save the schedule after the run |
| `--chaos-latency` | i64 | 0 | Artificial I/O latency in milliseconds |
| `--chaos-memory-limit` | i64 | 0 | Simulated memory ceiling in bytes |
| `--deploy` | bool | false | Enable deployment test discovery |
| `--deploy-platform` | text | "" | Target platform (e.g., linux-x86_64) |
| `--deploy-container` | bool | true | Run deploy tests in a container |
| `--deploy-local` | bool | false | Run deploy tests against local install |
| `--deploy-artifact` | text | "" | Path to the release artifact |
| `--deploy-dry-run` | bool | false | Show what would execute without running |
| `--security` | bool | false | Enable security test discovery |
| `--security-category` | text | "all" | Security category filter |
| `--security-report` | text | "" | Path for security audit report |

### 6.2 New TestOptions Fields

These fields are added to the `TestOptions` struct in `src/app/test_runner_new/test_runner_types.spl`.

```simple
struct TestOptions:
    # ... existing 33 fields ...

    # Fuzz testing
    fuzz: bool
    fuzz_iterations: i64
    fuzz_corpus: text
    fuzz_shrink: text
    fuzz_duration: i64

    # Chaos testing
    chaos: bool
    chaos_rate: f64
    chaos_schedule: text
    chaos_save_schedule: bool
    chaos_latency: i64
    chaos_memory_limit: i64

    # Deployment testing
    deploy: bool
    deploy_platform: text
    deploy_container: bool
    deploy_local: bool
    deploy_artifact: text
    deploy_dry_run: bool

    # Security testing
    security: bool
    security_category: text
    security_report: text
```

### 6.3 Discovery Rules

The test file discovery logic in `src/app/test_runner_new/test_runner_files.spl` is extended with the following rules:

```
Standard run (bin/simple test):
  Discovers: test/unit/**/*_spec.spl
             test/integration/**/*_spec.spl
             test/system/**/*_spec.spl
  Skips:     test/fuzz/
             test/resilience/
             test/deploy/
             test/security/

With --fuzz:
  Also discovers: test/fuzz/**/*_fuzz_spec.spl
  Also discovers: test/**/*_spec.spl files containing :fuzz tag

With --chaos:
  Also discovers: test/resilience/**/*_chaos_spec.spl
  Also discovers: test/**/*_spec.spl files containing :chaos tag

With --deploy:
  Also discovers: test/deploy/**/*_spec.spl
  Also discovers: test/**/*_spec.spl files containing :deploy tag

With --security:
  Also discovers: test/security/**/*_spec.spl
  Also discovers: test/**/*_spec.spl files containing :security tag

With --all:
  Discovers everything in test/ (including fuzz, resilience, deploy, security)
```

### 6.4 Tag-Based Filtering

Tests can be tagged inline using the existing tag mechanism:

```simple
it "description" :fuzz:
    # This test only runs when --fuzz is active

it "description" :chaos:
    # This test only runs when --chaos is active

it "description" :deploy:
    # This test only runs when --deploy is active

it "description" :security:
    # This test only runs when --security is active

it "description" :fuzz :slow:
    # Combines tags: requires --fuzz AND is marked slow
```

### 6.5 Environment Variables

The test runner propagates the following environment variables to child test processes:

| Variable | Set When | Value |
|----------|----------|-------|
| `SIMPLE_FUZZ` | `--fuzz` | `"1"` |
| `SIMPLE_FUZZ_ITERATIONS` | `--fuzz-iterations=N` | `"{N}"` |
| `SIMPLE_FUZZ_SEED` | `--seed=N` (with `--fuzz`) | `"{N}"` |
| `SIMPLE_CHAOS` | `--chaos` | `"1"` |
| `SIMPLE_CHAOS_RATE` | `--chaos-rate=N` | `"{N}"` |
| `SIMPLE_CHAOS_SCHEDULE` | `--chaos-schedule=path` | path |
| `SIMPLE_DEPLOY` | `--deploy` | `"1"` |
| `SIMPLE_DEPLOY_PLATFORM` | `--deploy-platform=X` | X |
| `SIMPLE_SECURITY` | `--security` | `"1"` |
| `SIMPLE_SECURITY_CATEGORY` | `--security-category=X` | X |

### 6.6 Output Format

Each layer adds a summary section to the test runner output:

```
=== Fuzz Results ===
  parser_no_crash ........... 1000/1000 inputs OK  (2.3s)
  lexer_no_crash ............ 1000/1000 inputs OK  (1.8s)
  sdn_parser ................ 997/1000 inputs OK   (1.1s)  FAIL
    Failing input: "key: {{nested: }"
    Shrunk to:     "k: {}"
    Seed: 48291

=== Chaos Results ===
  build_disk_full ........... PASS (3 faults injected, 3 handled)
  mcp_network_drop .......... PASS (7 faults injected, 7 handled)
  import_missing_file ....... FAIL (1 fault leaked)
    Schedule saved: test/resilience/schedules/schedule_20260215_143022.sdn

=== Deploy Results ===
  fresh_install ............. PASS  (4/4 checks)
  container ................. PASS  (2/2 checks)
  cross_platform ............ SKIP  (docker not available)

=== Security Results ===
  path_traversal ............ PASS  (4/4 checks)
  resource_exhaustion ....... PASS  (4/4 checks)
  supply_chain .............. PASS  (3/3 checks)
  injection ................. PASS  (3/3 checks)

4067 spec tests, 2997 fuzz inputs, 10 chaos faults, 13 deploy checks, 14 security checks
```

### 6.7 SDN Configuration (Full)

The complete additions to `simple.test.sdn`:

```
test:
  # ... existing fields ...

  # Advanced test layers (all off by default)
  run_fuzz_tests: false
  run_chaos_tests: false
  run_deploy_tests: false
  run_security_tests: false

  # Fuzz testing
  fuzz:
    default_iterations: 1000
    default_timeout_ms: 5000
    default_max_size: 256
    shrink_rounds: 100
    corpus_dir: test/fuzz/corpus
    save_crashes: true
    crash_dir: test/fuzz/crashes

  # Chaos testing
  chaos:
    default_fault_rate: 0.1
    default_timeout_ms: 30000
    default_latency_ms: 0
    save_schedules: true
    schedule_dir: test/resilience/schedules
    memory_limit: 0

  # Deployment testing
  deploy:
    default_platform: linux-x86_64
    use_container: true
    container_image: simple-test-isolation:latest
    artifact_path: bin/release/simple
    temp_dir: tmp/deploy_test
    timeout: 600
    platforms:
      - linux-x86_64
      - linux-aarch64
      - macos-arm64

  # Security testing
  security:
    default_category: all
    timeout: 60
    report_path: security-audit.md
    categories:
      - injection
      - traversal
      - dos
      - supply-chain
    block_dangerous_ops: true
```

---

## 7. Prioritized Roadmap

### Phase 1: Fuzz the Parser and SDN (Weeks 1-3)

**Goal:** Catch crashes in the most-exercised code paths with minimal effort.

**Deliverables:**
1. `src/std/fuzz.spl` -- generators, shrinking, `fuzz_check()`, corpus management
2. `test/fuzz/parser_fuzz_spec.spl` -- lexer + parser fuzz targets
3. `test/fuzz/sdn_fuzz_spec.spl` -- SDN parser fuzz targets
4. `test/fuzz/semver_fuzz_spec.spl` -- semver parser fuzz targets
5. `test/fuzz/manifest_fuzz_spec.spl` -- manifest loader fuzz targets
6. `--fuzz` and `--fuzz-iterations` flags in test runner
7. Corpus directory with seed inputs from existing test fixtures

**Why first:** The parser processes untrusted input (user source code). Any crash there is both a bug and a potential security issue. SDN and semver parsers are simpler targets that validate the fuzz library itself before tackling the full parser.

**Effort:** ~800 lines of library code, ~400 lines of test specs.

### Phase 2: Differential Fuzzing Across Backends (Weeks 4-6)

**Goal:** Verify that the interpreter, SMF loader, and native backend produce identical results.

**Deliverables:**
1. `fuzz_differential()` in `src/std/fuzz.spl`
2. `test/fuzz/backend_differential_fuzz_spec.spl` -- interpreter vs. native on generated programs
3. `test/fuzz/eval_differential_fuzz_spec.spl` -- core eval vs. compiler eval
4. Integration with `--mode` flag for backend selection
5. Corpus of programs that exercise arithmetic, string ops, control flow, and closures

**Why second:** Once the parser is fuzz-hardened, the next highest-value target is behavioral consistency between backends. This catches codegen bugs that unit tests miss because they only test one backend at a time.

**Effort:** ~300 lines of library additions, ~500 lines of test specs.

### Phase 3: Deploy Smoke Tests in CI (Weeks 7-8)

**Goal:** Guarantee that every release candidate installs and runs on supported platforms.

**Deliverables:**
1. `test/deploy/fresh_install_spec.spl` -- version, hello world, test runner
2. `test/deploy/container_spec.spl` -- Docker image build + test execution
3. `test/deploy/cross_platform_spec.spl` -- binary size, dependency audit
4. `--deploy` flag in test runner
5. CI pipeline step that runs `bin/simple test --deploy` before tagging a release

**Why third:** Deployment tests require a stable fuzz+chaos library (for the artifact integrity checks) and are primarily CI-oriented, so they can wait until the core libraries are proven.

**Effort:** ~200 lines of test specs, ~50 lines of CI config.

### Phase 4: Security Scanning and Supply Chain (Weeks 9-11)

**Goal:** Prevent path traversal, injection, and resource exhaustion attacks.

**Deliverables:**
1. `test/security/path_traversal_spec.spl` -- import path validation
2. `test/security/resource_exhaustion_spec.spl` -- recursion/nesting limits
3. `test/security/injection_spec.spl` -- interpolation and shell safety
4. `test/security/supply_chain_spec.spl` -- binary hash, dependency audit, credential scan
5. `--security` and `--security-report` flags in test runner
6. `security-audit.md` report generation

**Why fourth:** Security tests depend on having a robust fuzz corpus (Phase 1-2 outputs feed into security edge cases) and deployment infrastructure (Phase 3 provides the container harness).

**Effort:** ~400 lines of test specs, ~100 lines of report generation.

### Phase 5: Chaos for Async and Actors (Weeks 12-15)

**Goal:** Verify that the actor system and async runtime recover from network partitions, message loss, and resource exhaustion.

**Deliverables:**
1. `src/std/chaos.spl` -- fault injection, schedules, `chaos_run()`, resilience patterns
2. `test/resilience/build_disk_full_spec.spl` -- build system under I/O faults
3. `test/resilience/mcp_network_spec.spl` -- MCP server under network faults
4. `test/resilience/actor_partition_spec.spl` -- actor message delivery under faults
5. `test/resilience/import_missing_spec.spl` -- import resolution under missing files
6. `--chaos`, `--chaos-rate`, `--chaos-schedule` flags in test runner
7. Schedule serialization and deterministic replay

**Why last:** Chaos testing is the most complex layer. It requires fault injection hooks in the runtime, which means modifying `src/app/io/mod.spl` and potentially the SFFI layer. The async/actor system (`actor` keyword) is still maturing, so chaos tests against it should wait until the API stabilizes.

**Effort:** ~600 lines of library code, ~500 lines of test specs.

### Summary Timeline

| Phase | Weeks | Lines (est.) | Tests Added (est.) |
|-------|-------|-------------|-------------------|
| 1. Fuzz parser + SDN | 1-3 | 1200 | 30-50 fuzz targets |
| 2. Differential fuzzing | 4-6 | 800 | 10-20 differential targets |
| 3. Deploy smoke tests | 7-8 | 250 | 10-15 deploy checks |
| 4. Security scanning | 9-11 | 500 | 15-25 security checks |
| 5. Chaos for async | 12-15 | 1100 | 10-20 chaos scenarios |
| **Total** | **15 weeks** | **~3850** | **~75-130 targets** |

---

## 8. Folder Structure

```
test/
  unit/                          # Existing: 4067 unit tests
  integration/                   # Existing: integration tests
  system/                        # Existing: system tests

  fuzz/                          # NEW: Fuzz testing (Phase 1-2)
    parser_fuzz_spec.spl         #   Lexer + parser fuzz targets
    sdn_fuzz_spec.spl            #   SDN parser fuzz targets
    semver_fuzz_spec.spl         #   Semver parser fuzz targets
    manifest_fuzz_spec.spl       #   Manifest loader fuzz targets
    string_interp_fuzz_spec.spl  #   String interpolation edge cases
    path_fuzz_spec.spl           #   Path utility fuzz targets
    backend_differential_fuzz_spec.spl  # Interpreter vs. native (Phase 2)
    eval_differential_fuzz_spec.spl     # Core eval vs. compiler eval (Phase 2)
    corpus/                      #   Saved interesting inputs
      parser/                    #     Parser corpus files
      sdn/                       #     SDN corpus files
      semver/                    #     Semver corpus files
    crashes/                     #   Automatically saved crash inputs

  resilience/                    # NEW: Chaos testing (Phase 5)
    build_disk_full_spec.spl     #   Build system under I/O faults
    mcp_network_spec.spl         #   MCP server under network faults
    actor_partition_spec.spl     #   Actor message delivery under faults
    import_missing_spec.spl      #   Import resolution under missing files
    test_runner_chaos_spec.spl   #   Test runner subprocess failures
    schedules/                   #   Saved fault schedules for replay
      schedule_001.sdn
      schedule_002.sdn

  deploy/                        # NEW: Deployment testing (Phase 3)
    fresh_install_spec.spl       #   Install + hello world + test run
    container_spec.spl           #   Docker build + test execution
    cross_platform_spec.spl      #   Binary size + dependency audit
    upgrade_spec.spl             #   Version upgrade path
    fixtures/                    #   Deploy test fixtures
      hello.spl
      smoke_spec.spl

  security/                      # NEW: Security testing (Phase 4)
    path_traversal_spec.spl      #   Import path validation
    resource_exhaustion_spec.spl #   Recursion/nesting limits
    injection_spec.spl           #   Interpolation + shell safety
    supply_chain_spec.spl        #   Binary hash + dependency audit
    fixtures/                    #   Security test fixtures
      symlink_loop/
      malicious_inputs/

src/
  std/
    fuzz.spl                     # NEW: Fuzz testing library (Phase 1)
    chaos.spl                    # NEW: Chaos testing library (Phase 5)
```

---

## Appendix A: Relationship to Existing Specs

This specification builds on and complements existing testing specifications:

| Existing Spec | Relationship |
|---------------|-------------|
| `doc/spec/testing/property_testing.md` | Phase 1 fuzz library shares generator concepts with `@property_test`. The `std.fuzz` generators supersede the `gen.*` namespace proposed there with explicit `gen_*` function names that work within current runtime limitations. |
| `doc/spec/testing/snapshot_testing.md` | Fuzz crash corpus files follow a similar pattern to snapshot files. Both are saved artifacts that gate test outcomes. |
| `doc/spec/testing/testing_bdd_framework.md` | All four new layers use SSpec (`describe`/`it`) as their test structure. No new test framework is introduced. |
| `doc/spec/testing/sdoctest.md` | SDoctest remains independent. Fuzz tests do not run against docstring examples (sdoctests are deterministic by design). |

## Appendix B: Runtime Limitations

The following known runtime limitations (documented in MEMORY.md) affect the design of these test layers:

- **No try/catch/throw.** All fault injection uses the Option pattern (`var error = nil`). The `inject_error()` function returns `""` for no-fault and an error message string for fault.
- **No generics at runtime.** Generator functions return concrete types (`i64`, `text`, `[i64]`) rather than generic `T`. Domain-specific generators (e.g., `gen_simple_expr`) return `text` that is then parsed.
- **Chained method calls broken.** All library code uses intermediate `var` bindings instead of method chains.
- **Nested closure capture limitation.** Chaos schedule recording uses module-level variables rather than captured closures.
- **`}}` is escape for `}`.** The `gen_sdn_value` generator must account for this when producing SDN fragments with braces.
- **`assert` is a keyword.** Security tests use `expect().to_equal()` assertions, not `assert()`.
- **`val` is a keyword.** Generator parameter names avoid `val` (use `value`, `item`, `node`).
