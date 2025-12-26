# Multi-Language Tooling Implementation Plan

**Date:** 2025-12-26
**Feature Range:** #1180-1199 (20 features)
**Status:** 📋 Planning Phase
**Dependencies:** Tree-sitter Implementation (#1156-1179) ✅ Complete

## Executive Summary

Implement comprehensive development tooling for multi-language projects using the Tree-sitter foundation. This enables building, testing, and deploying applications that combine Simple with other languages (Rust, Python, JavaScript, etc.) in a unified workflow.

**Key Benefits:**
- **Polyglot Projects**: Single tool chain for multiple languages
- **Unified Build System**: Incremental compilation across languages
- **Cross-Language Testing**: Integrated test runner with multi-language support
- **Streamlined Deployment**: Package and deploy multi-language apps
- **Developer Experience**: Watch mode, hot reload, error aggregation

**Foundation:**
- Tree-sitter parser (#1156-1179) provides multi-language parsing
- Grammar support for: Simple, Rust, Python, JavaScript/TypeScript, Go, C/C++
- Language detection and AST traversal infrastructure ready

**Timeline:** 15-22 days (3 phases)
**Implementation:** Self-hosted in Simple language (`simple/std_lib/src/tooling/`)

---

## Architecture

### Three-Layer Design

```
┌─────────────────────────────────────────────────────┐
│  CLI Layer (simple build, simple test, simple deploy)│
│  - Argument parsing                                  │
│  - Command dispatch                                  │
│  - User feedback                                     │
└──────────────────┬──────────────────────────────────┘
                   │
┌──────────────────┴──────────────────────────────────┐
│  Tooling Core (Orchestration & Coordination)        │
│  - Multi-language compiler interface                │
│  - Test runner & discovery                          │
│  - Deployment pipeline                              │
│  - Dependency tracking & incremental builds         │
│  - Error aggregation & reporting                    │
└──────────────────┬──────────────────────────────────┘
                   │
┌──────────────────┴──────────────────────────────────┐
│  Language Adapters (Per-Language Integration)       │
│  - Simple: Native compiler integration              │
│  - Rust: cargo wrapper (build, test, clippy)        │
│  - Python: pytest, mypy, setuptools                 │
│  - JavaScript: npm/webpack, jest                    │
│  - Go: go build, go test                            │
└─────────────────────────────────────────────────────┘
```

### Module Structure

```
simple/std_lib/src/tooling/
├── __init__.spl              # Public API exports
├── core/                     # Core orchestration
│   ├── __init__.spl
│   ├── project.spl           # Project detection & config (200 lines)
│   ├── dependency.spl        # Dependency tracking (250 lines)
│   ├── incremental.spl       # Incremental compilation (220 lines)
│   └── errors.spl            # Error aggregation (180 lines)
├── compiler/                 # Compiler interface
│   ├── __init__.spl
│   ├── interface.spl         # Multi-language interface (200 lines)
│   ├── simple.spl            # Simple compiler adapter (150 lines)
│   ├── rust.spl              # Rust/cargo adapter (180 lines)
│   ├── python.spl            # Python adapter (160 lines)
│   ├── javascript.spl        # JS/TS adapter (170 lines)
│   └── build_system.spl      # Build orchestration (240 lines)
├── testing/                  # Testing tools
│   ├── __init__.spl
│   ├── runner.spl            # Multi-language test runner (250 lines)
│   ├── discovery.spl         # Test discovery (200 lines)
│   ├── coverage.spl          # Coverage reporting (220 lines)
│   ├── parallel.spl          # Parallel execution (180 lines)
│   ├── filter.spl            # Test filtering (140 lines)
│   └── aggregation.spl       # Result aggregation (160 lines)
├── deployment/               # Deployment tools
│   ├── __init__.spl
│   ├── packaging.spl         # Multi-language packaging (230 lines)
│   ├── bundling.spl          # Artifact bundling (190 lines)
│   ├── pipeline.spl          # Deployment pipeline (210 lines)
│   ├── containers.spl        # Container image gen (240 lines)
│   ├── optimization.spl      # Binary optimization (180 lines)
│   ├── automation.spl        # Release automation (200 lines)
│   ├── versioning.spl        # Version management (150 lines)
│   └── templates.spl         # Config templates (170 lines)
└── watch/                    # Watch mode
    ├── __init__.spl
    ├── watcher.spl           # File system watcher (200 lines)
    └── reload.spl            # Hot reload (180 lines)

simple/app/tooling/           # CLI applications
├── build/
│   └── main.spl              # simple build (120 lines)
├── test/
│   └── main.spl              # simple test (140 lines)
└── deploy/
    └── main.spl              # simple deploy (130 lines)

simple/std_lib/test/unit/tooling/  # Tests
├── compiler_spec.spl         # Compiler tests
├── testing_spec.spl          # Testing tools tests
├── deployment_spec.spl       # Deployment tests
└── integration_spec.spl      # Integration tests
```

**Total Implementation:** ~5,760 lines across 32 modules

---

## Feature Breakdown

### Phase 1: Compiler & Build Tools (6 features, 5-7 days)

#### #1180 - Multi-Language Compiler Interface (Difficulty: 4)
**Purpose:** Unified interface for compiling different languages

**Implementation:** `tooling/compiler/interface.spl` (200 lines)

**Features:**
- Language-agnostic compilation interface
- Adapter pattern for language-specific compilers
- Compilation result standardization
- Error/warning normalization
- Incremental compilation support

**API:**
```simple
use tooling.compiler

# Detect project type and compile
let result = compiler.compile(
    path: ".",
    languages: [:simple, :rust, :python],
    mode: :release,
    incremental: true
)

match result:
    Ok(artifacts):
        for artifact in artifacts:
            print(f"Built: {artifact.path}")
    Err(errors):
        for error in errors:
            print(f"{error.file}:{error.line}: {error.message}")
```

**Language Adapters:**
- **Simple**: Direct compiler API integration
- **Rust**: Shell out to `cargo build`
- **Python**: Byte-compile `.py` files, run mypy
- **JavaScript**: Run webpack/rollup/esbuild
- **Go**: Shell out to `go build`

#### #1181 - Incremental Compilation Support (Difficulty: 5)
**Purpose:** Only recompile changed files and dependencies

**Implementation:** `tooling/core/incremental.spl` (220 lines)

**Features:**
- File modification tracking (mtime, content hash)
- Dependency graph construction
- Change propagation analysis
- Partial recompilation
- Build cache management

**API:**
```simple
use tooling.compiler

let cache = IncrementalCache.load(".build_cache")

# Only recompile changed files
let result = compiler.compile_incremental(
    cache: cache,
    changed_files: ["app.spl", "lib.rs"]
)

# 10x faster for large projects
print(f"Recompiled {result.files_built} files in {result.duration_ms}ms")
```

**Algorithm:**
1. Detect file changes (mtime or SHA256)
2. Build dependency graph via imports/includes
3. Mark changed files and transitive deps as dirty
4. Recompile only dirty files
5. Update cache with new mtimes/hashes

#### #1182 - Build System Integration (Difficulty: 4)
**Purpose:** Orchestrate builds across multiple languages

**Implementation:** `tooling/compiler/build_system.spl` (240 lines)

**Features:**
- Multi-language build orchestration
- Parallel compilation
- Build order determination
- Artifact management
- Build script execution

**API:**
```simple
use tooling.compiler

let build = BuildSystem.new(".")

# Auto-detect project structure
build.discover_languages()  # → [:simple, :rust, :python]

# Configure build
build.set_mode(:release)
build.set_parallel(4)
build.set_optimization(:size)

# Execute build
let result = build.execute()
print(f"Built {result.artifacts.len()} artifacts")
```

**Build Phases:**
1. **Discovery**: Find all language roots (Cargo.toml, package.json, etc.)
2. **Planning**: Determine build order (respecting inter-language deps)
3. **Compilation**: Execute language-specific builds in parallel
4. **Linking**: Combine artifacts (if needed for FFI)
5. **Post-processing**: Strip symbols, compress, etc.

#### #1183 - Dependency Tracking (Difficulty: 4)
**Purpose:** Track dependencies within and across languages

**Implementation:** `tooling/core/dependency.spl` (250 lines)

**Features:**
- Intra-language dependency graphs (imports/includes)
- Inter-language FFI dependency tracking
- Circular dependency detection
- Dependency visualization
- Change impact analysis

**API:**
```simple
use tooling.core

let tracker = DependencyTracker.new(".")

# Build full dependency graph
tracker.analyze_all_languages()

# Find dependencies of a file
let deps = tracker.get_dependencies("app.spl")
print(f"app.spl depends on: {deps}")

# Find reverse dependencies
let rdeps = tracker.get_reverse_dependencies("lib.spl")
print(f"Files depending on lib.spl: {rdeps}")

# Detect circular dependencies
let cycles = tracker.detect_cycles()
if cycles.len() > 0:
    print("Warning: circular dependencies found:")
    for cycle in cycles:
        print(f"  {cycle.join(' -> ')}")
```

**Graph Construction:**
- Parse all files with Tree-sitter
- Extract import/include statements
- Build directed graph (file → dependencies)
- Compute transitive closure for impact analysis

#### #1184 - Error Aggregation Across Languages (Difficulty: 3)
**Purpose:** Collect and normalize errors from all languages

**Implementation:** `tooling/core/errors.spl` (180 lines)

**Features:**
- Error normalization (file, line, column, message, severity)
- Multi-language error parsing (rustc, mypy, eslint, etc.)
- Error deduplication
- Severity classification
- Formatted output (terminal, JSON, XML)

**API:**
```simple
use tooling.core

let aggregator = ErrorAggregator.new()

# Add errors from multiple sources
aggregator.add_rust_errors(rust_output)
aggregator.add_python_errors(mypy_output)
aggregator.add_simple_errors(simple_errors)

# Get normalized errors
let errors = aggregator.get_all()
for error in errors:
    print(f"{error.file}:{error.line}:{error.column}: {error.severity}: {error.message}")

# Group by file
let by_file = aggregator.group_by_file()
for (file, errors) in by_file:
    print(f"{file}: {errors.len()} errors")
```

**Error Parsers:**
- **Rust**: Parse rustc/cargo output (JSON mode)
- **Python**: Parse mypy, pylint output
- **JavaScript**: Parse ESLint, TypeScript output
- **Simple**: Native diagnostic integration

#### #1185 - Watch Mode & Hot Reload (Difficulty: 3)
**Purpose:** Automatically rebuild on file changes

**Implementation:** `tooling/watch/watcher.spl` (200 lines), `tooling/watch/reload.spl` (180 lines)

**Features:**
- File system watching (cross-platform)
- Debounced rebuilds (avoid rebuild storms)
- Incremental recompilation
- Hot module replacement (HMR)
- Development server integration

**API:**
```simple
use tooling.watch

# Start watch mode
let watcher = Watcher.new(".")

watcher.on_change(fn(changed_files):
    print(f"Files changed: {changed_files}")
    let result = compiler.compile_incremental(changed_files)

    if result.is_ok():
        print("✓ Build succeeded, reloading...")
        reload.notify_clients()
    else:
        print(f"✗ Build failed: {result.errors}")
)

watcher.start()  # Blocks, watching for changes
```

**Watch Strategy:**
- Use OS-native file watching (inotify on Linux, FSEvents on macOS, ReadDirectoryChangesW on Windows)
- Debounce events (300ms delay to batch rapid changes)
- Filter ignored files (.git, node_modules, target)
- Trigger incremental rebuild on file save

---

### Phase 2: Testing Tools (6 features, 5-7 days)

#### #1186 - Multi-Language Test Runner (Difficulty: 4)
**Purpose:** Run tests across all languages in a project

**Implementation:** `tooling/testing/runner.spl` (250 lines)

**Features:**
- Unified test execution interface
- Language-specific test adapters
- Test result normalization
- Progress reporting
- Failure handling and retry

**API:**
```simple
use tooling.testing

let runner = TestRunner.new(".")

# Auto-detect test frameworks
runner.discover_tests()  # → cargo test, pytest, jest, spec tests

# Run all tests
let result = runner.run_all(
    parallel: true,
    fail_fast: false,
    verbose: true
)

print(f"Tests: {result.passed}/{result.total} passed")
print(f"Time: {result.duration_ms}ms")
```

**Test Adapters:**
- **Simple**: Native spec framework integration
- **Rust**: `cargo test` wrapper
- **Python**: `pytest` wrapper
- **JavaScript**: `jest` or `mocha` wrapper
- **Go**: `go test` wrapper

#### #1187 - Test Discovery Across Languages (Difficulty: 4)
**Purpose:** Find all tests in a multi-language project

**Implementation:** `tooling/testing/discovery.spl` (200 lines)

**Features:**
- Language-specific test discovery patterns
- Recursive directory scanning
- Test file filtering (naming conventions)
- Test function/method extraction
- Test grouping by module/file

**API:**
```simple
use tooling.testing

let discovery = TestDiscovery.new(".")

# Find all tests
let tests = discovery.discover_all()

print(f"Found {tests.len()} test suites:")
for suite in tests:
    print(f"  {suite.language}: {suite.path} ({suite.test_count} tests)")

# Filter by language
let python_tests = discovery.discover_by_language(:python)

# Filter by pattern
let integration_tests = discovery.discover_by_pattern("integration")
```

**Discovery Patterns:**
- **Simple**: `*_spec.spl`, `*_test.spl`
- **Rust**: Files with `#[test]` or `#[cfg(test)]`
- **Python**: `test_*.py`, `*_test.py`, classes/functions named `test*`
- **JavaScript**: `*.test.js`, `*.spec.js`, `describe()` blocks
- **Go**: `*_test.go`

#### #1188 - Coverage Reporting (Multi-Language) (Difficulty: 4)
**Purpose:** Generate code coverage reports across languages

**Implementation:** `tooling/testing/coverage.spl` (220 lines)

**Features:**
- Per-language coverage collection
- Coverage normalization (% lines/branches)
- Cross-language aggregation
- HTML/XML/JSON report generation
- Coverage threshold enforcement

**API:**
```simple
use tooling.testing

let coverage = CoverageReporter.new(".")

# Run tests with coverage
let result = coverage.run_with_coverage(
    languages: [:simple, :rust, :python]
)

# Generate reports
coverage.generate_html("target/coverage/html")
coverage.generate_json("target/coverage/coverage.json")

# Check thresholds
if result.total_coverage < 80.0:
    fail("Coverage below 80%: {result.total_coverage}%")

print(f"Coverage: {result.total_coverage}%")
print(f"  Simple: {result.simple_coverage}%")
print(f"  Rust: {result.rust_coverage}%")
print(f"  Python: {result.python_coverage}%")
```

**Coverage Tools:**
- **Simple**: Native coverage instrumentation
- **Rust**: `cargo-tarpaulin` or `cargo-llvm-cov`
- **Python**: `coverage.py`
- **JavaScript**: `jest --coverage` or `nyc`
- **Go**: `go test -cover`

#### #1189 - Test Result Aggregation (Difficulty: 3)
**Purpose:** Combine test results from multiple languages

**Implementation:** `tooling/testing/aggregation.spl` (160 lines)

**Features:**
- Result normalization (passed/failed/skipped)
- Failure reason extraction
- Timing aggregation
- Flaky test detection
- JUnit XML generation

**API:**
```simple
use tooling.testing

let aggregator = TestAggregator.new()

# Add results from different test runners
aggregator.add_simple_results(simple_tests)
aggregator.add_rust_results(cargo_test_output)
aggregator.add_python_results(pytest_output)

# Get summary
let summary = aggregator.get_summary()
print(f"{summary.passed} passed, {summary.failed} failed, {summary.skipped} skipped")

# Export JUnit XML (for CI systems)
aggregator.export_junit_xml("test-results.xml")

# Detect flaky tests (passed sometimes, failed other times)
let flaky = aggregator.detect_flaky_tests()
for test in flaky:
    print(f"Warning: flaky test {test.name}")
```

#### #1190 - Parallel Test Execution (Difficulty: 4)
**Purpose:** Run tests in parallel for faster feedback

**Implementation:** `tooling/testing/parallel.spl` (180 lines)

**Features:**
- Test suite parallelization
- Worker pool management
- Load balancing
- Isolation (separate processes/threads)
- Result streaming

**API:**
```simple
use tooling.testing

let executor = ParallelExecutor.new(
    workers: 4,
    isolation: :process
)

# Run tests in parallel
let result = executor.run_parallel(test_suites, fn(suite):
    return run_test_suite(suite)
)

# 4x speedup on 4-core machine
print(f"Ran {result.total_tests} tests in {result.duration_ms}ms")
```

**Parallelization Strategy:**
- Split test suites across N workers
- Use process pool for isolation (avoid shared state)
- Stream results as they complete
- Collect and merge results at end

#### #1191 - Test Filtering & Selection (Difficulty: 3)
**Purpose:** Run subset of tests based on filters

**Implementation:** `tooling/testing/filter.spl` (140 lines)

**Features:**
- Filter by test name pattern
- Filter by language
- Filter by file/module
- Filter by tags/markers
- Changed-file-only testing

**API:**
```simple
use tooling.testing

let filter = TestFilter.new()

# Filter by pattern
filter.by_pattern("integration")  # Only integration tests

# Filter by language
filter.by_language(:rust)

# Filter by changed files (smart testing)
let changed_files = git.get_changed_files("HEAD~1")
filter.by_changed_files(changed_files)

let tests = filter.apply(all_tests)
print(f"Running {tests.len()} filtered tests")
```

**Smart Testing:**
- Detect changed files from git diff
- Use dependency graph to find affected tests
- Run only tests that cover changed code
- 10x faster CI for small changes

---

### Phase 3: Deployment Tools (8 features, 5-8 days)

#### #1192 - Multi-Language Packaging (Difficulty: 4)
**Purpose:** Package artifacts from multiple languages into deployable units

**Implementation:** `tooling/deployment/packaging.spl` (230 lines)

**Features:**
- Multi-language artifact collection
- Native binary packaging
- Python wheel/sdist generation
- JavaScript npm package
- Manifest generation

**API:**
```simple
use tooling.deployment

let packager = Packager.new(".")

# Package all artifacts
let package = packager.create_package(
    name: "my-app",
    version: "1.0.0",
    include: [:simple, :rust, :python],
    format: :tarball
)

package.write("my-app-1.0.0.tar.gz")
print(f"Package size: {package.size_mb}MB")
```

#### #1193 - Artifact Bundling (Difficulty: 3)
**Purpose:** Bundle multiple artifacts into single deployable

**Implementation:** `tooling/deployment/bundling.spl` (190 lines)

**Features:**
- Asset bundling (binaries, libraries, resources)
- Dependency bundling (shared libraries)
- Script bundling (startup scripts)
- Configuration bundling
- Compression

**API:**
```simple
use tooling.deployment

let bundler = Bundler.new()

bundler.add_binary("target/release/app")
bundler.add_library("target/release/libapp.so")
bundler.add_scripts("scripts/start.sh")
bundler.add_config("config/production.toml")

let bundle = bundler.create_bundle("app-bundle.tar.gz")
print(f"Bundle contains {bundle.file_count} files")
```

#### #1194 - Deployment Pipeline Integration (Difficulty: 4)
**Purpose:** Integrate with deployment systems (Docker, K8s, etc.)

**Implementation:** `tooling/deployment/pipeline.spl` (210 lines)

**Features:**
- Pipeline configuration (stages, environments)
- Deployment strategies (blue-green, canary, rolling)
- Health checks
- Rollback support
- Webhook notifications

**API:**
```simple
use tooling.deployment

let pipeline = DeploymentPipeline.new()

# Define stages
pipeline.add_stage(:build, fn():
    compiler.compile_all()
)

pipeline.add_stage(:test, fn():
    testing.run_all()
)

pipeline.add_stage(:deploy_staging, fn():
    deploy_to_env(:staging)
)

pipeline.add_stage(:deploy_production, fn():
    deploy_to_env(:production)
)

# Execute pipeline
let result = pipeline.execute()
if result.is_ok():
    print("✓ Deployment succeeded")
```

#### #1195 - Container Image Generation (Difficulty: 4)
**Purpose:** Generate Docker/OCI container images

**Implementation:** `tooling/deployment/containers.spl` (240 lines)

**Features:**
- Dockerfile generation
- Multi-stage build support
- Layer optimization
- Base image selection
- Image tagging and pushing

**API:**
```simple
use tooling.deployment

let container = ContainerBuilder.new()

# Auto-generate Dockerfile
container.detect_runtime()  # → :simple_native, :rust, :python
container.set_base_image("alpine:3.18")
container.add_artifacts("target/release/app")
container.set_entrypoint("/app/app")

# Build image
let image = container.build(
    tag: "my-app:1.0.0",
    platform: [:linux_amd64, :linux_arm64]
)

# Push to registry
image.push("docker.io/user/my-app:1.0.0")
```

**Generated Dockerfile:**
```dockerfile
FROM alpine:3.18 AS builder
COPY . /build
WORKDIR /build
RUN simple build --release

FROM alpine:3.18
COPY --from=builder /build/target/release/app /app/app
ENTRYPOINT ["/app/app"]
```

#### #1196 - Binary Stripping & Optimization (Difficulty: 3)
**Purpose:** Reduce binary size for deployment

**Implementation:** `tooling/deployment/optimization.spl` (180 lines)

**Features:**
- Debug symbol stripping
- Dead code elimination
- Binary compression (UPX, etc.)
- Size analysis and reporting
- Optimization level selection

**API:**
```simple
use tooling.deployment

let optimizer = BinaryOptimizer.new()

# Optimize binary
let result = optimizer.optimize(
    binary: "target/release/app",
    strip_symbols: true,
    compress: true,
    level: :aggressive
)

print(f"Original size: {result.original_size_mb}MB")
print(f"Optimized size: {result.optimized_size_mb}MB")
print(f"Reduction: {result.reduction_percent}%")
```

**Optimization Techniques:**
- Strip debug symbols (`strip` command)
- Link-time optimization (LTO)
- Compress with UPX (if viable)
- Remove unused sections

#### #1197 - Release Automation (Difficulty: 3)
**Purpose:** Automate the release process

**Implementation:** `tooling/deployment/automation.spl` (200 lines)

**Features:**
- Git tag creation
- Changelog generation (from commits)
- GitHub/GitLab release creation
- Artifact upload (binaries, packages)
- Notification (Slack, email)

**API:**
```simple
use tooling.deployment

let release = ReleaseAutomation.new()

# Create release
release.set_version("1.0.0")
release.generate_changelog("v0.9.0..HEAD")
release.create_git_tag()
release.build_artifacts(platforms: [:linux, :macos, :windows])
release.create_github_release(
    repo: "user/my-app",
    title: "Release 1.0.0",
    draft: false
)
release.upload_artifacts()
release.notify_slack("#releases", "Released v1.0.0!")

print("✓ Release 1.0.0 complete")
```

#### #1198 - Version Management (Difficulty: 3)
**Purpose:** Manage versioning across multi-language projects

**Implementation:** `tooling/deployment/versioning.spl` (150 lines)

**Features:**
- Semantic versioning (SemVer)
- Version bumping (major/minor/patch)
- Multi-file version synchronization
- Version validation
- Pre-release/build metadata

**API:**
```simple
use tooling.deployment

let version = VersionManager.new(".")

# Current version
print(f"Current version: {version.get_current()}")  # → 1.0.0

# Bump version
version.bump(:minor)  # → 1.1.0

# Update all version files
version.sync_all([
    "Cargo.toml",
    "package.json",
    "pyproject.toml",
    "simple.toml"
])

print(f"New version: {version.get_current()}")  # → 1.1.0
```

#### #1199 - Deploy Configuration Templates (Difficulty: 3)
**Purpose:** Generate deployment configurations from templates

**Implementation:** `tooling/deployment/templates.spl` (170 lines)

**Features:**
- Template engine (variable substitution)
- Environment-specific configs
- Kubernetes YAML generation
- Docker Compose generation
- Systemd unit file generation

**API:**
```simple
use tooling.deployment

let templates = TemplateGenerator.new()

# Generate Kubernetes deployment
templates.generate_kubernetes(
    app_name: "my-app",
    image: "my-app:1.0.0",
    replicas: 3,
    env: :production
)
# → deployment.yaml, service.yaml, ingress.yaml

# Generate Docker Compose
templates.generate_docker_compose(
    services: [:web, :api, :db],
    networks: [:frontend, :backend]
)
# → docker-compose.yml

# Generate systemd unit
templates.generate_systemd(
    service_name: "my-app",
    binary: "/usr/local/bin/my-app",
    user: "app"
)
# → my-app.service
```

---

## API Design Examples

### Example 1: Multi-Language Build

```simple
use tooling

# Create multi-language project
let project = tooling.Project.new(".")

# Configure build
project.add_language(:simple, root: "app/")
project.add_language(:rust, root: "lib/rust/")
project.add_language(:python, root: "lib/python/")

# Build all
let result = project.build(
    mode: :release,
    parallel: true,
    incremental: true
)

match result:
    Ok(artifacts):
        print(f"✓ Built {artifacts.len()} artifacts")
    Err(errors):
        print(f"✗ Build failed with {errors.len()} errors")
        for error in errors:
            print(f"  {error}")
```

### Example 2: Comprehensive Test Suite

```simple
use tooling.testing

# Run all tests
let runner = TestRunner.new(".")

let result = runner.run_all(
    parallel: true,
    coverage: true,
    filter: "integration"
)

# Generate coverage report
runner.generate_coverage_html("target/coverage/")

# Check quality gates
if result.coverage < 80.0:
    fail("Coverage below threshold")

if result.failed > 0:
    fail(f"{result.failed} tests failed")

print(f"✓ All tests passed ({result.total} tests, {result.coverage}% coverage)")
```

### Example 3: Complete Deployment Pipeline

```simple
use tooling

# Define deployment pipeline
let pipeline = tooling.DeploymentPipeline.new(".")

# Build stage
pipeline.stage("build", fn():
    tooling.build_all(mode: :release, optimize: true)
)

# Test stage
pipeline.stage("test", fn():
    tooling.test_all(parallel: true, coverage: true)
)

# Package stage
pipeline.stage("package", fn():
    tooling.package(
        format: :tarball,
        include: [:binaries, :libraries, :configs]
    )
)

# Deploy stage
pipeline.stage("deploy", fn():
    tooling.deploy_to_kubernetes(
        cluster: "production",
        namespace: "default",
        replicas: 3
    )
)

# Execute pipeline
pipeline.execute()
```

---

## Testing Strategy

### Unit Tests (20+ tests)

**Test Files:**
- `simple/std_lib/test/unit/tooling/compiler_spec.spl`
- `simple/std_lib/test/unit/tooling/testing_spec.spl`
- `simple/std_lib/test/unit/tooling/deployment_spec.spl`
- `simple/std_lib/test/unit/tooling/integration_spec.spl`

**Test Coverage:**
- Compiler interface tests (language adapter registration, compilation, error handling)
- Incremental compilation tests (change detection, dependency graph, cache management)
- Test runner tests (discovery, execution, result aggregation)
- Deployment tests (packaging, bundling, container generation)
- Version management tests (SemVer parsing, bumping, synchronization)

### Integration Tests (5+ tests)

**Test Scenarios:**
1. Build multi-language project (Simple + Rust + Python)
2. Run tests across all languages with coverage
3. Deploy to Docker container
4. Watch mode with incremental rebuild
5. Full pipeline execution (build → test → package → deploy)

### Example Test

```simple
use spec
use tooling.compiler

describe "Multi-language compilation":
    context "when compiling Simple + Rust project":
        it "builds both languages successfully":
            let project = create_test_project([
                "app.spl" → "fn main(): print(\"Hello\")",
                "lib/Cargo.toml" → "[package]\nname = \"lib\"",
                "lib/src/lib.rs" → "pub fn hello() {}"
            ])

            let result = compiler.compile(
                path: project.root,
                languages: [:simple, :rust]
            )

            expect(result).to_be_ok()
            expect(result.artifacts.len()).to_equal(2)

        it "aggregates errors from both languages":
            let project = create_test_project([
                "app.spl" → "fn main(): invalid_syntax",
                "lib/src/lib.rs" → "pub fn hello() { invalid }"
            ])

            let result = compiler.compile(path: project.root)

            expect(result).to_be_err()
            let errors = result.unwrap_err()
            expect(errors.len()).to_be_greater_than(0)
            expect(errors.any(fn(e): e.language == :simple)).to_be_true()
            expect(errors.any(fn(e): e.language == :rust)).to_be_true()
```

---

## Documentation

### Specification Document

**File:** `doc/spec/tooling.md` (800+ lines)

**Contents:**
1. Introduction & Motivation
2. Multi-Language Compilation
3. Incremental Builds & Dependency Tracking
4. Testing Framework
5. Deployment Tools
6. Watch Mode & Hot Reload
7. API Reference
8. Language Adapter Guide
9. Configuration
10. Best Practices
11. Examples

### User Guide

**File:** `doc/guides/multi_language_tooling.md` (500+ lines)

**Contents:**
- Getting started
- Building multi-language projects
- Running tests
- Deploying applications
- Continuous integration
- Common workflows
- Troubleshooting

---

## Implementation Timeline

### Phase 1: Compiler & Build Tools (5-7 days)
- Day 1-2: Multi-language compiler interface (#1180) + language adapters
- Day 3: Incremental compilation (#1181)
- Day 4: Build system integration (#1182) + dependency tracking (#1183)
- Day 5: Error aggregation (#1184)
- Day 6-7: Watch mode & hot reload (#1185)

**Milestone:** Can build multi-language projects with incremental compilation

### Phase 2: Testing Tools (5-7 days)
- Day 8-9: Multi-language test runner (#1186) + discovery (#1187)
- Day 10: Coverage reporting (#1188)
- Day 11: Test result aggregation (#1189) + parallel execution (#1190)
- Day 12-14: Test filtering (#1191) + integration testing

**Milestone:** Can run and report tests across all languages

### Phase 3: Deployment Tools (5-8 days)
- Day 15-16: Multi-language packaging (#1192) + bundling (#1193)
- Day 17: Deployment pipeline (#1194)
- Day 18: Container image generation (#1195)
- Day 19: Binary optimization (#1196)
- Day 20: Release automation (#1197) + versioning (#1198)
- Day 21-22: Config templates (#1199) + documentation + polish

**Milestone:** Complete deployment pipeline from build to production

**Total Timeline:** 15-22 days

---

## Success Criteria

### Functionality
- ✅ Build multi-language projects (Simple + Rust + Python + JavaScript)
- ✅ Incremental compilation (10x faster for small changes)
- ✅ Run tests across all languages with unified reporting
- ✅ Generate code coverage reports
- ✅ Package and deploy multi-language apps
- ✅ Watch mode with hot reload
- ✅ Generate Docker containers
- ✅ Automate releases

### Performance
- ✅ Incremental builds: 10x faster than clean builds for 1-file changes
- ✅ Parallel testing: N-core speedup for N workers
- ✅ Test discovery: <1s for projects with 1000+ tests
- ✅ Coverage reporting: <5s overhead

### Developer Experience
- ✅ Single command for multi-language builds: `simple build`
- ✅ Single command for all tests: `simple test`
- ✅ Single command for deployment: `simple deploy`
- ✅ Watch mode just works: `simple build --watch`
- ✅ Clear error messages from all languages
- ✅ Unified configuration (simple.toml)

### Code Quality
- ✅ 20+ unit tests (80%+ coverage)
- ✅ 5+ integration tests (end-to-end scenarios)
- ✅ Comprehensive documentation (1300+ lines)
- ✅ Self-hosted in Simple language
- ✅ Follows Simple language best practices

---

## Dependencies

### External Tools
- **Rust**: cargo (build, test)
- **Python**: pip, pytest, mypy
- **JavaScript**: npm, jest, webpack
- **Go**: go (build, test)
- **Docker**: docker (for container builds)
- **Git**: git (for change detection, versioning)

### Internal Dependencies
- **Tree-sitter (#1156-1179)**: Multi-language parsing ✅ Complete
- **File I/O**: Read/write files, directory traversal
- **Process execution**: Shell out to language-specific tools
- **JSON**: Parse tool output, generate reports
- **TOML**: Configuration parsing

---

## Future Enhancements

### Short Term
1. **Language Plugins**: Plugin system for adding new languages
2. **Remote Caching**: Distributed build cache (Bazel-style)
3. **Build Reproducibility**: Hermetic builds, content-addressable cache
4. **Dependency Locking**: Multi-language lock file

### Medium Term
5. **Cloud Builds**: Offload builds to cloud infrastructure
6. **Distributed Testing**: Run tests across multiple machines
7. **Advanced Profiling**: Performance profiling across languages
8. **Security Scanning**: Multi-language vulnerability detection

### Long Term
9. **Build Visualization**: Interactive build graph explorer
10. **AI-Assisted Debugging**: LLM integration for error analysis
11. **Cross-Language Refactoring**: Refactor across language boundaries
12. **Unified Package Registry**: Single registry for all languages

---

## Metrics

**Implementation:**
- **Lines of Code:** ~5,760 lines across 32 modules
- **Modules Created:** 32 (core: 4, compiler: 6, testing: 6, deployment: 8, watch: 2, CLI: 3, tests: 4)
- **Documentation:** 1300+ lines (spec + guide)
- **Features:** 20 (6 compiler + 6 testing + 8 deployment)
- **Timeline:** 15-22 days

**Testing:**
- **Unit Tests:** 20+ tests
- **Integration Tests:** 5+ tests
- **Coverage Target:** 80%+

**Impact:**
- Enables polyglot Simple projects
- 10x faster incremental builds
- Unified tooling across all languages
- Streamlined deployment pipeline
- Developer productivity boost

---

## Conclusion

Multi-Language Tooling provides comprehensive build, test, and deployment infrastructure for polyglot Simple projects. By leveraging the Tree-sitter foundation and following Simple language best practices, we enable developers to seamlessly work with multiple languages in a unified, efficient workflow.

**Key Benefits:**
- **Unified Interface**: Single tool chain for all languages
- **Incremental Everything**: Fast feedback for large projects
- **Production Ready**: Complete deployment pipeline
- **Developer Friendly**: Watch mode, hot reload, clear errors
- **Self-Hosted**: All tooling written in Simple

**Next Steps After Completion:**
1. Implement MCP-MCP multi-language support (#1230-1259) - 30 features
2. Implement MCP-MCP tooling integration (#1260-1279) - 20 features
3. Add UI framework support (#1369-1378) - 10 features

This foundation enables the entire MCP-MCP ecosystem (61 remaining features) and positions Simple as a first-class choice for multi-language development.
