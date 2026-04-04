# Simple Language

[![Production Ready](https://img.shields.io/badge/status-production%20ready-brightgreen)](doc/archive/release/PRODUCTION_READY_SUMMARY.md)
[![Tests](https://img.shields.io/badge/tests-4067%2F4067%20passing-brightgreen)](doc/09_report/session/full_test_suite_results_2026-02-14.md)
[![LLVM Cross](https://github.com/simple-lang/simple/actions/workflows/simple-llvm-cross.yml/badge.svg)](.github/workflows/simple-llvm-cross.yml)
[![License](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE)

Simple is a self-hosted language and toolchain that combines a readable Python-like surface with compiler-integrated testing, documentation, architecture rules, and baremetal-oriented execution paths.

The repo is unusually broad: language, compiler, interpreter, loader, test runner, doc generation, traceability tooling, SDN-backed project databases, editor tooling, and hardware-oriented test flows all live together.

**Quick Navigation:** [Distinctive Features](#distinctive-features) | [Feature Status](#feature-status-highlights) | [Quick Start](#quick-start) | [Language Basics](#language-basics) | [Examples](#examples) | [Editor Plugins](#editor-plugins) | [Documentation](#documentation)

---

## Distinctive Features

- **Self-hosted staged toolchain**: real source layers for frontend, type analysis, borrow checking, backend, driver, interpreter, and loader live in-tree.
- **Verification-native workflow**: SSpec BDD tests, SDoctest executable docs, coverage, traceability checks, and generated spec docs are part of the toolchain rather than bolted on.
- **MDSOC architecture support**: virtual capsules, manifests, and architecture-aware repository structure are first-class concepts.
- **Parser-friendly macro system**: macro definitions, expansion, validation, and hygiene are compiler features rather than editor-hostile text substitution.
- **Math-oriented syntax blocks**: `m{}`, `loss{}`, and `nograd{}` are implemented syntax with parsing, evaluation, five rendering backends (text, debug, Unicode, LaTeX, Markdown), and editor integration (query/LSP hover, VSCode highlighting/preview, Neovim inline Unicode preview with conceal).
- **SDN-backed textual databases**: tests, todos, dashboards, and other project metadata are stored through repo-native SDN data flows.
- **Multiple execution paths**: interpreter, loader, SMF/module loading, and native/LLVM-oriented compilation paths coexist in one system.
- **Baremetal-oriented build and test plumbing**: QEMU, semihosting, remote baremetal flows, and adapter-backed hardware lanes are built into the repo story.
- **Tooling-aware language rules**: Tree-sitter integration, primitive-public-API linting, traceability tooling, and language statistics are part of the platform.
- **Shared UI testing surface**: the UI test client can drive both web backends and the TUI web proxy through one HTTP-oriented test interface.

## Feature Status Highlights

Implemented and safe to advertise:
- SSpec, SDoctest, coverage, traceability checks, and generated spec docs
- SSpec mock policy: system-test mock ban, HAL-only and custom pattern modes
- Self-hosted staged compiler, interpreter, and loader architecture
- MDSOC manifests and architecture-focused project structure
- Parser-friendly macros with validation and hygiene
- Tree-sitter outline/query tooling
- SDN-backed project, test, and todo databases
- Primitive-public-API linting and semantic wrapper/unit-type patterns
- Borrow-checking infrastructure
- Watch mode and auto-build support
- mmap-backed loader support and executable-memory plumbing
- Baremetal build/test plumbing and host-aware remote baremetal flows

Implemented, but best described with qualifiers:
- `m{}` / `loss{}` / `nograd{}` are real and usable, but the broader DL story is still evolving
- LLVM support is real, but some paths still depend on external LLVM tooling
- GC and no-GC runtime families: 5 public families (`common`, `nogc_sync_mut`, `nogc_async_mut`, `gc_async_mut`, `nogc_async_mut_noalloc`) with compiler boundary enforcement, interpreter warnings, and target preset mapping. Support matrix: [doc/04_architecture/runtime_family_support_matrix.md](doc/04_architecture/runtime_family_support_matrix.md)
- Shared UI testing across web and TUI-web surfaces is real, but this is not yet one finished unified UI layer
- Remote baremetal execution is real, but some hardware lanes remain host- and board-dependent

Complete with bounded scope:
- AOP provides predicate-based pointcuts (`execution`, `within`, `attr`), deterministic before/after/around advice, compile-time weaving as the default backend, and scoped runtime interception. Support matrix: [doc/05_design/aop_support_matrix.md](doc/05_design/aop_support_matrix.md)

Complete with bounded scope:
- VHDL backend compiles a documented hardware-oriented Simple subset to synthesizable VHDL-2008, validated through GHDL analysis/elaboration. Strict fail-fast on unsupported constructs. Simulation-backed execution is a follow-on milestone. Support matrix: [doc/04_architecture/vhdl_support_matrix.md](doc/04_architecture/vhdl_support_matrix.md)

Experimental or partial:
- C/C++ bidirectional interop has substantial SFFI infrastructure, but not enough evidence to present it as fully complete. Current state: [doc/05_design/sffi_bidirectional_interop.md](doc/05_design/sffi_bidirectional_interop.md)
- Lean generation, artifact inventory, and proof-checking commands exist, but the supported end-to-end formal verification workflow is still partial. Current state: [doc/03_plan/lean_verification_implementation.md](doc/03_plan/lean_verification_implementation.md)

See [doc/report/unique_features.md](doc/report/unique_features.md) for the evidence-backed audit.

---

## Runtime Families

Simple organizes its standard library into runtime families based on allocation, mutation, and concurrency requirements:

| Family | Allocation | Mutation | Async | Use Case |
|--------|-----------|----------|-------|----------|
| `common` | heap (default) | immutable | no | Pure functions, math, text, encoding |
| `nogc_sync_mut` | heap/arena/pool | mutable | no | File I/O, networking, FFI, databases |
| `nogc_async_mut` | heap | mutable | yes | Async I/O, threads, actors, generators |
| `gc_async_mut` | GC-managed | mutable | yes | GPU/CUDA, ML pipelines |
| `nogc_async_mut_noalloc` | stack only | mutable | yes | Baremetal, embedded, RTOS |

The compiler enforces family boundaries: importing a GC module from a no-GC context produces a diagnostic warning. Target presets (`Baremetal`, `Hosted`, `EmbeddedWithHeap`) automatically restrict module resolution to compatible families.

For advanced use: `nogc_async_immut` provides persistent data structures with lock-free concurrency.

See [Runtime Family Support Matrix](doc/04_architecture/runtime_family_support_matrix.md) for full contracts, and [Known Limitations](doc/08_tracking/bug/gc_runtime_limitations.md) for current caveats.

---

## Quick Start

### Installation from Binary (Recommended)

Download the pre-compiled release for your platform - no build required!

**What you get:**
- Pre-compiled runtime (10 MB optimized binary)
- Complete Simple compiler (100% Simple source code)
- Standard library (100% Simple)
- All development tools (MCP server, LSP, debugger - all in Simple)

**Available platforms:**
- Linux x86_64 / ARM64
- macOS x86_64 / ARM64
- Windows x86_64 / ARM64

```bash
# Linux x86_64
wget https://github.com/simple-lang/simple/releases/download/v0.6.1/simple-0.6.1-linux-x86_64.tar.gz
tar -xzf simple-0.6.1-linux-x86_64.tar.gz
cd simple-0.6.1
export PATH="$PWD/bin:$PATH"
simple --version

# macOS ARM64 (Apple Silicon)
curl -LO https://github.com/simple-lang/simple/releases/download/v0.6.1/simple-0.6.1-darwin-aarch64.tar.gz
tar -xzf simple-0.6.1-darwin-aarch64.tar.gz
cd simple-0.6.1
export PATH="$PWD/bin:$PATH"
simple --version

# Windows x86_64 (PowerShell)
Invoke-WebRequest -Uri https://github.com/simple-lang/simple/releases/download/v0.6.1/simple-0.6.1-windows-x86_64.zip -OutFile simple.zip
Expand-Archive simple.zip
cd simple-0.6.1
$env:PATH = "$PWD\bin;$env:PATH"
simple --version
```

**Note:** The runtime is pre-compiled for performance, but the entire language implementation (compiler, stdlib, tools) is in Simple source code that you can read and modify!

### From Source (Developers Only)

Only needed if you want to modify the runtime:

```bash
git clone https://github.com/simple-lang/simple.git
cd simple

# Linux bootstrap verification
scripts/bootstrap/bootstrap-from-scratch.sh --output=bootstrap
```

Direct commands behind the wrapper:

```bash
src/compiler_rust/target/bootstrap/simple --version
bin/release/simple build bootstrap
sha256sum bootstrap/simple_stage2 bootstrap/simple_stage3
```

See [doc/08_tracking/build/bootstrap_multi_platform.md](doc/08_tracking/build/bootstrap_multi_platform.md) and [doc/03_plan/pure_simple_bootstrap.plan.md](doc/03_plan/pure_simple_bootstrap.plan.md) for the current bootstrap flow.

### Build with GPU Support

```bash
simple build --release --features=vulkan
```

### Your First Program

```sdoctest
# hello.spl
>>> fn main() -> i64:
...     0  # Entry point, returns exit code
```

```bash
# Run it
simple hello.spl
echo $?  # Prints: 0
```

---

## CLI Usage

The `simple` command works like Python:

```
Usage:
  simple                      Start interactive REPL
  simple <file.spl>           Run source file
  simple <file.smf>           Run compiled binary
  simple -c "code"            Run code string
  simple compile <src> [-o <out>]  Compile to SMF
  simple watch <file.spl>     Watch and auto-recompile

Build System (Self-Hosting):
  simple build                Build the project (debug)
  simple build --release      Release build (optimized)
  simple build --bootstrap    Bootstrap build (minimal 9.3MB)
  simple build test           Run all tests
  simple build coverage       Generate coverage reports
  simple build lint           Run linter (clippy)
  simple build fmt            Format code (rustfmt)
  simple build check          Run all quality checks
  simple build clean          Clean build artifacts
  simple build --help         Show all build options

Options:
  -h, --help     Show help
  -v, --version  Show version
  -c <code>      Run code string
  --gc-log       Enable verbose GC logging
  --gc=off       Disable garbage collection
```

### Examples

```bash
# Interactive REPL
simple
>>> 1 + 2
3
>>> x = 10
>>> x * 5
50
>>> exit

# Run a program
echo "main = 42" > hello.spl
simple hello.spl
echo $?  # Exit code: 42

# Compile to binary
simple compile hello.spl
simple hello.smf  # Run the compiled binary

# Watch mode (auto-recompile on changes)
simple watch app.spl
```

---

## Language Basics

### Variables & Types

```sdoctest
# Variables - immutable by default, mutable with var
>>> x = 10
>>> x
10
>>> var y = 20
>>> y
20
>>> PI = 3.14159
>>> PI
3.14159

# Type inference works automatically
>>> count = 100
>>> count
100

# Basic types inferred
>>> a = 42
>>> a
42
>>> pi = 3.14159
>>> flag = true
>>> flag
true

# String interpolation default
>>> name = "world"
>>> msg = "Hello, {name}!"
>>> print msg
Hello, world!
```

### Control Flow

```sdoctest
# If/else with indentation
>>> var x = 5
>>> if x > 0:
...     print "positive"
... elif x < 0:
...     print "negative"
... else:
...     print "zero"
positive

# Loops
>>> for i in 0..3:
...     print i
0
1
2

>>> while x > 3:
...     x = x - 1
>>> x
3
```

### Functions

```sdoctest
>>> fn add(a: i64, b: i64) -> i64:
...     a + b  # Implicit return

>>> fn greet(greeting: text):
...     print "Hello, {greeting}!"

# Function calls
>>> sum = add(1, 2)
>>> sum
3
>>> greet("Alice")
Hello, Alice!

# Lambdas with backslash
>>> double = \x: x * 2
>>> nums = [1, 2, 3, 4, 5]
>>> evens = nums.filter(\x: x % 2 == 0)
>>> evens
[2, 4]
```

### Structs & Classes

```simple
# Structs (value types)
struct Point:
    x: f64
    y: f64

p = Point(x: 1.0, y: 2.0)

# Classes (reference types)
class Person:
    name: text
    age: i64

    fn greet():
        print "Hi, {self.name}!"

alice = Person(name: "Alice", age: 30)
alice.greet()
```

### Collections

```sdoctest
# Arrays - short form (no val)
>>> nums = [1, 2, 3, 4, 5]
>>> first = nums[0]
>>> first
1

# Collection methods
>>> count = nums.len()
>>> count
5

# Dictionary (short form)
>>> scores = {"alice": 100, "bob": 85}
>>> alice_score = scores["alice"]
>>> alice_score
100

# Filter with lambda
>>> odds = nums.filter(\x: x % 2 == 1)
>>> odds
[1, 3, 5]
>>> big_nums = nums.filter(\x: x > 3)
>>> big_nums
[4, 5]

# Tuples
>>> pair = (1, "hello")
>>> num = pair.0
>>> num
1
>>> msg = pair.1
>>> msg
"hello"

# List comprehensions
>>> squared = [x * x for x in 0..5]
>>> squared
[0, 1, 4, 9, 16]
>>> evens = [x for x in nums if x % 2 == 0]
>>> evens
[2, 4]
```

### Unit Types (Postfix Literals)

Type-safe units prevent mixing incompatible values:

```simple
# Define unit types with postfix syntax
unit length(base: f64):
    mm = 0.001, cm = 0.01, m = 1.0, km = 1000.0

unit velocity(base: f64) = length / time:
    mps = 1.0, kmph = 0.277778, mph = 0.44704

unit UserId: i64 as uid
unit OrderId: i64 as oid

# Usage with postfix literals
height = 175_cm              # Length type
width = 10_cm + 5_mm         # Auto-converts to same base
speed = 200_kmph             # Velocity type
distance = 42_km             # Length type

# Type safety - compile error:
# bad = height + speed       # Error: can't add Length + Velocity

# Semantic IDs prevent mix-ups
user = 42_uid                # UserId
order = 100_oid              # OrderId
# wrong: UserId = 100_oid    # Error: OrderId ≠ UserId

# Computed units
travel_time = distance / speed    # Returns Time type
print("ETA: {travel_time.to_min()} minutes")
```

### Pattern Matching

```simple
enum Shape:
    Circle(radius: f64)
    Rectangle(width: f64, height: f64)
    Square(side: f64)
    Triangle(base: f64, height: f64)

# Pattern matching with case syntax
fn area(s: Shape) -> f64:
    match s:
        case Circle(r):
            3.14159 * r * r  # Implicit return
        case Rectangle(w, h):
            w * h
        case Square(side):
            side * side
        case Triangle(b, h):
            0.5 * b * h

# Preferred arrow syntax (shorter)
fn perimeter(s: Shape) -> f64:
    match s:
        | Circle(r) -> 2.0 * 3.14159 * r
        | Rectangle(w, h) -> 2.0 * (w + h)
        | Square(side) -> 4.0 * side
        | Triangle(a, b, c) -> a + b + c

# Pattern matching with nil (not None)
fn get_radius(opt: Option<f64>) -> f64:
    match opt:
        | Some(r) -> r
        | nil -> 0.0  # Use nil instead of None
```

### Parser-Friendly Macros

Simple macros are contract-first and LL(1) parseable - the IDE can provide autocomplete without expanding the macro:

```simple
# Macro declares what it introduces in the contract header
macro define_counter(NAME: Str const) -> (
  returns result: (init: Int, step: Int),
  intro counter_fn: enclosing.class.fn "{NAME}Counter"(start: Int) -> Int
):
  const_eval:
    const init = 0
    const step = 1

  emit counter_fn:
    fn "{NAME}Counter"(start: Int) -> Int:
      start + step

# Usage - IDE knows about UserCounter before expansion
class Demo:
  define_counter!("User")

  fn run() -> Int:
    self.UserCounter(10)  # Autocomplete works!
```

**Built-in macros:**

```simple
# Print with formatting
println!("Hello, {name}!")           # Print with newline
print!("Value: {x}")                 # Print without newline

# Debug output with source location
dbg!(expression)                     # Prints: [file:line] expression = value

# Assertions
assert!(condition)                   # Panic if false
assert_eq!(a, b)                     # Panic if a != b
assert_ne!(a, b)                     # Panic if a == b

# Collections
nums = vec![1, 2, 3, 4, 5]           # Create vector
formatted = format!("x={x}")         # Format string without printing

# Panic with message
panic!("Something went wrong: {err}")
```

**Const-unrolled macro (generate multiple functions):**

```simple
# Generate accessor functions for each axis
macro gen_axes(BASE: Str const, N: Int const) -> (
  intro axes:
    for i in 0 .. N:
      enclosing.class.fn "{BASE}{i}"(v: Vec[N]) -> Int
):
  emit axes:
    for i in 0 .. N:
      fn "{BASE}{i}"(v: Vec[N]) -> Int:
        v[i]

# Usage: generates x(), y(), z() accessors
class Point3D:
  gen_axes!("axis_", 3)  # Creates axis_0, axis_1, axis_2
```

### AOP & Aspect-Oriented Programming

Predicate-based pointcuts with compile-time weaving as the default execution model:

```simple
# Before advice — runs before matching functions
on pc{ execution(* handle_request(..)) } use log_entry before priority 10

# After advice — runs after successful return
on pc{ execution(* save(..)) & attr(audited) } use audit_write after_success priority 20

# Around advice — wraps function with proceed() contract
on pc{ within(services.*) } use trace_around around priority 50

# Architecture rules — enforce layer dependencies at compile time
forbid pc{ within(hal.*) } "HAL cannot depend on services"
allow  pc{ within(services.*) } "Services can use HAL"
```

**Supported selectors:** `execution(*)`, `within(*)`, `attr(*)` with `&` (AND), `|` (OR), `!` (NOT) operators.
**Advice kinds:** `before`, `after_success`, `after_error`, `around` (proceed exactly-once).
**Ordering:** priority (descending) > specificity > lexicographic name.
**Zero overhead:** no weaving metadata when no aspects are defined.
**Runtime interception:** scoped, opt-in only, disabled in release builds.

See [AOP Support Matrix](doc/05_design/aop_support_matrix.md) for the full contract.

### SDN Configuration

Simple Data Notation - a minimal, token-efficient format for config files:

```sdn
# app.sdn - Application configuration
app:
    name: MyService
    version: 2.1.0

server:
    host: 0.0.0.0
    port: 8080
    workers: 4

# Inline arrays and dicts
features = [auth, logging, metrics]
database = {driver: postgres, host: localhost, port: 5432}

# Named tables - compact tabular data
rate_limits |endpoint, requests, window|
    /api/login, 5, 60
    /api/search, 100, 60
    /api/upload, 10, 300
```

Load SDN in Simple:

```simple
config = sdn::load("app.sdn")
print("Server port: {config.server.port}")
```

### SDoctest

Executable examples are part of the maintained test surface. Simple supports both demonstration blocks and verified `sdoctest` blocks, with `sdoctest` intended for examples that must run and match output.

```sdoctest
>>> factorial(5)
120
>>> factorial(0)
1
```

```simple
## Stack data structure with LIFO semantics
struct Stack:
    items: [i64]

var s = Stack(items: [])
s.items.push(1)
s.items.push(2)
print s.items.len()  # 2
```

Run SDoctest examples:
```bash
simple test --sdoctest README.md      # Run verified examples in Markdown/docs
simple test --sdoctest src/math.spl   # Run file-local doctest examples
simple test --sdoctest --tag slow     # Filter by tag
```

`--doctest` is still accepted as a compatibility alias, but `--sdoctest` is the clearer name for the implemented path.

### Functional Update Operator (`->`)

```simple
# The -> operator calls a method and assigns result back
var data = load_data()
data->normalize()        # data = data.normalize()
data->filter(min: 0)     # data = data.filter(min: 0)

# Chaining
data->normalize()->filter(min: 0)->save("out.txt")
```

### GPU Computing

```simple
import std.gpu

# GPU kernel style 1: #[gpu] with explicit bounds check
#[gpu]
fn vector_add_kernel(a: []f32, b: []f32, result: []f32):
    idx = gpu.global_id(0)           # Global thread index
    if idx < len(result):
        result[idx] = a[idx] + b[idx]

# GPU kernel style 2: @simd with auto bounds handling
@simd
fn vector_scale(data: []f32, scale: f32):
    val i = this.index()             # Global linear index (same as gpu.global_id())
    data[i] = data[i] * scale        # Bounds auto-handled

# Host function - runs on CPU
fn main():
    device = gpu.Device()

    # Allocate and upload data
    a = [1.0, 2.0, 3.0, 4.0]
    b = [5.0, 6.0, 7.0, 8.0]

    buf_a = device.alloc_buffer(a)
    buf_b = device.alloc_buffer(b)
    buf_result = device.alloc_buffer<f32>(4)

    # Launch kernel
    device.launch_1d(vector_add_kernel, [buf_a, buf_b, buf_result], 4)

    # Download results
    device.sync()
    result = device.download(buf_result)
    # result = [6.0, 8.0, 10.0, 12.0]
```

**GPU Thread Indexers:**

```simple
#[gpu]
fn matrix_multiply(A: []f32, B: []f32, C: []f32, N: u32):
    # Multi-dimensional indexing
    val row = gpu.global_id(0)       # First dimension
    val col = gpu.global_id(1)       # Second dimension

    # Thread group (workgroup) info
    val local_row = gpu.local_id(0)  # Index within workgroup
    val group_row = gpu.group_id(0)  # Workgroup index

    # Alternative @simd style
    # val(row, col) = this.index()  # Tuple for 2D
    # vallocal_idx = this.thread_index()
    # valgroup_idx = this.group_index()

    if row < N and col < N:
        var sum = 0.0_f32
        for k in 0..N:
            sum += A[row * N + k] * B[k * N + col]
        C[row * N + col] = sum
```

**GPU Examples:** See `examples/gpu/vulkan/` for vector add, matrix multiply, reduction, and image blur.

---

## Documentation

### Quick Links by Topic

| Topic | Description | Link |
|-------|-------------|------|
| **Docs Hub** | Numbered documentation index | [doc/README.md](doc/README.md) |
| **Language Spec** | Executable and generated specs | [doc/06_spec/README.md](doc/06_spec/README.md) |
| **Guides** | Practical how-to guides | [doc/07_guide/README.md](doc/07_guide/README.md) |
| **Plans** | Implementation roadmap | [doc/03_plan/README.md](doc/03_plan/README.md) |
| **Research** | Design explorations | [doc/01_research/README.md](doc/01_research/README.md) |
| **Architecture** | System design principles | [doc/04_architecture/README.md](doc/04_architecture/README.md) |
| **Tracking** | Bugs, tests, and todo tracking | [doc/08_tracking/README.md](doc/08_tracking/README.md) |
| **Reports** | Session and milestone reports | [doc/09_report/README.md](doc/09_report/README.md) |
| **Deep Learning** | Neural networks and GPU computing | [doc/07_guide/deep_learning/deep_learning.md](doc/07_guide/deep_learning/deep_learning.md) |

### Core Documentation

**Getting Started:**
- [Documentation Hub](doc/README.md) - Current entry point for the numbered doc tree
- [Getting Started](doc/07_guide/getting_started.md) - Project setup and first steps
- [Syntax Quick Reference](doc/07_guide/quick_reference/syntax_quick_reference.md) - Canonical public syntax cheat sheet
- [Testing Guide](doc/07_guide/testing/testing.md) - Testing workflow and command surface

**Language Reference:**
- [Syntax Guide](doc/07_guide/language/syntax.md) - Surface syntax and examples
- [Type System Guide](doc/07_guide/language/type_system.md) - Types, mutability, and usage
- [Module System Guide](doc/07_guide/language/module_system.md) - Imports, packages, and layout
- [Standard Library Guide](doc/07_guide/library/stdlib.md) - Stdlib organization and usage

**GPU Computing:**
- [Deep Learning Guide](doc/07_guide/deep_learning/deep_learning.md) - Pure Simple, model-oriented, and training flows
- [GPU Programming Guide](doc/07_guide/backend/gpu_programming.md) - Backend and kernel-oriented GPU usage
- [GPU API](doc/api/gpu_api.md) - API-level GPU reference
- [LLVM Backend Architecture](doc/04_architecture/LLVM_BACKEND_ARCHITECTURE.md) - Backend implementation details

**Development:**
- [Build Guide](doc/07_guide/build.md) - Building Simple and common workflows
- [Testing Guide](doc/07_guide/testing/testing.md) - Test runner behavior and flags
- [Mock Policy Guide](doc/07_guide/testing/mock_policy_system_test_ban.md) - System test mock ban and test level enforcement
- [Coverage Guide](doc/07_guide/testing/coverage.md) - Coverage, SDoctest, and enforcement
- [MCP Tooling Guide](doc/07_guide/tooling/mcp.md) - MCP registration and usage

**Advanced Features:**
- [Macro System](doc/06_spec/macro.md) - Executable macro spec and status
- [AOP Support Matrix](doc/05_design/aop_support_matrix.md) - Supported selectors, advice kinds, backends, and error codes
- [SDN Format](doc/04_architecture/format/note_sdn_index.md) - Note/SDN storage and indexing format
- [SDoctest](doc/06_spec/app/compiler/modules/testing/sdoctest.md) - Documentation testing and verified examples
- [Feature Documentation](doc/06_spec/feature.md) - Generated feature-doc artifact format

---

## Examples

### Deep Learning Examples

Simple ships multiple deep learning examples across pure-Simple, model-training, and GPU-oriented flows:

**Pure Simple Neural Networks:**
```bash
# XOR neural network training
bin/simple examples/pure_nn/xor_training_example.spl

# Linear regression (learns y = 2x + 1)
bin/simple examples/pure_nn/simple_regression.spl

# Iris flower classification
bin/simple examples/pure_nn/iris_classification.spl
```

**MedGemma Korean Fine-Tuning:**
```bash
# Progressive LoRA training to prevent catastrophic forgetting
bin/simple examples/medgemma_korean/run_all.spl
```

**CUDA Programming:**
```bash
# Direct CUDA C API - multi-GPU, streams, events
bin/simple examples/cuda/basic.spl
```

**See [Deep Learning Guide](doc/07_guide/deep_learning/deep_learning.md) for current documentation.**

### Other Examples

The `examples/` directory contains additional working examples:

| Example | Description |
|---------|-------------|
| `cli_demo.spl` | Command-line argument parsing |
| `file_async_basic.spl` | Async file I/O operations |
| `ui_todo_app.spl` | Cross-platform UI application |
| `vulkan_triangle.spl` | GPU rendering with Vulkan |
| `async_tcp_echo_server.spl` | Async TCP networking |

Run an example:
```bash
bin/simple examples/cli_demo.spl
```

---

## BDD Feature Documentation

Feature documentation is auto-generated from BDD spec tests. Each spec defines feature metadata and executable assertions that verify the feature works correctly.

```simple
# simple/std_lib/test/features/infrastructure/lexer_spec.spl
import std.spec

feature "Lexer":
    """
    The lexer tokenizes Simple source code into tokens.
    Feature ID: #1
    Category: infrastructure
    """

    scenario "tokenizes keywords":
        given "source code with keywords"
        when "the lexer processes it"
        then "it produces keyword tokens"
        expect tokenize("fn main") to contain Token(Keyword, "fn")

    scenario "handles indentation":
        given "indented code blocks"
        when "the lexer processes it"
        then "it emits INDENT and DEDENT tokens"
```

Run feature tests:
```bash
# Run a specific feature spec
./target/debug/simple simple/std_lib/test/features/infrastructure/lexer_spec.spl

# Generate documentation from tests
./target/debug/simple simple/std_lib/test/features/generate_docs.spl
```

Generated docs land in the numbered documentation tree, primarily under `doc/06_spec/`, so the checked examples stay close to the current spec artifacts.

---

## Grammar & Specification

### Language Grammar

Simple’s current language references are split between the guide tree for user-facing explanations and the spec tree for executable or generated reference material.

**Current Reference Documents:**
- [Syntax Quick Reference](doc/07_guide/quick_reference/syntax_quick_reference.md) - Fast public-language reference
- [Syntax Guide](doc/07_guide/language/syntax.md) - User-facing language walkthrough
- [Language Spec Index](doc/06_spec/README.md) - Current generated spec index
- [Syntax Spec](doc/06_spec/syntax.md) - Spec artifact for syntax coverage
- [Types Spec](doc/06_spec/types.md) - Spec artifact for type-system coverage
- [Modules Spec](doc/06_spec/modules.md) - Spec artifact for module-system coverage

**Quick Grammar Reference:**

```
# Top-level
program ::= statement*

# Statements
statement ::= function_def | class_def | struct_def | enum_def
            | import_stmt | export_stmt | expr_stmt

# Expressions (Pratt parser)
expr ::= literal | identifier | binary_op | unary_op
       | call | index | field_access | lambda
       | if_expr | match_expr | block

# Types
type ::= identifier | array_type | tuple_type | fn_type
       | optional_type | result_type | generic_type

# Literals
literal ::= integer | float | string | bool | array | dict | tuple
```

### Specification Index

The current spec and guide material is organized under the numbered documentation tree:

**Core Language:**
- [Syntax Spec](doc/06_spec/syntax.md) - Syntax-oriented spec material
- [Types Spec](doc/06_spec/types.md) - Type-system spec material
- [Data Structures Spec](doc/06_spec/data_structures.md) - Data-structure coverage
- [Functions Spec](doc/06_spec/functions.md) - Functions and pattern matching
- [Traits Spec](doc/06_spec/traits.md) - Traits and implementations
- [Memory Spec](doc/06_spec/memory.md) - Ownership and borrowing
- [Modules Spec](doc/06_spec/modules.md) - Import/export system

**Advanced Features:**
- [Concurrency Spec](doc/06_spec/concurrency.md) - Async and concurrency behavior
- [Metaprogramming Spec](doc/06_spec/metaprogramming.md) - Macros and decorators
- [Macro Spec](doc/06_spec/macro.md) - Macro-specific executable coverage
- [Capability Effects](doc/06_spec/capability_effects.md) - Capability/effect system
- [Standard Library Guide](doc/07_guide/library/stdlib.md) - Stdlib structure and usage
- [SFFI Guide](doc/07_guide/ffi/sffi.md) - Interop guidance

**Testing & Tooling:**
- [Testing Guide](doc/07_guide/testing/testing.md) - Test runner and matchers
- [Coverage Guide](doc/07_guide/testing/coverage.md) - Coverage and SDoctest enforcement
- [Lint Guide](doc/07_guide/tooling/lint.md) - Lint rules and workflow
- [MCP Guide](doc/07_guide/tooling/mcp.md) - MCP workflow and registration

**GPU & Platform:**
- [GPU Programming Guide](doc/07_guide/backend/gpu_programming.md) - GPU usage
- [Deep Learning Guide](doc/07_guide/deep_learning/deep_learning.md) - Model-oriented examples
- [Baremetal Guide](doc/07_guide/backend/baremetal.md) - Platform and baremetal flows

See [doc/README.md](doc/README.md), [doc/06_spec/README.md](doc/06_spec/README.md), and [doc/07_guide/README.md](doc/07_guide/README.md) for the current documentation entry points.

---

## Project Structure

```
simple/
├── bin/                      # CLI entry points
│   ├── simple               # Main CLI (shell wrapper)
│   └── release/             # Pre-built release binaries
│       └── simple           # Pre-built runtime (33 MB)
│
├── src/                      # Simple source code (100% Simple)
│   ├── app/                  # Applications
│   │   ├── cli/             # Main CLI dispatcher
│   │   ├── build/           # Self-hosting build system
│   │   ├── mcp/             # MCP server (Model Context Protocol)
│   │   ├── lsp/             # Language server protocol
│   │   ├── io/              # SFFI wrappers (file, process, etc.)
│   │   └── ...              # 50+ tool modules
│   ├── lib/                  # Libraries
│   │   ├── database/        # Unified database (BugDB, TestDB, etc.)
│   │   └── pure/            # Pure Simple DL (tensor, autograd, nn)
│   ├── std/                  # Standard library
│   │   ├── src/             # Library source
│   │   └── test/            # Library tests
│   └── compiler/             # Compiler infrastructure
│       ├── backend/         # Code generation
│       ├── inference/       # Type inference
│       └── parser/          # Parser and treesitter
│
├── examples/                 # Example programs
│   ├── pure_nn/             # Deep learning examples
│   └── gpu/vulkan/          # GPU computing examples
│
├── test/                     # Test suites
│   ├── integration/         # Integration tests
│   ├── system/              # System tests
│   └── intensive/           # Intensive feature tests
│
├── doc/                      # Documentation
│   ├── spec/                # Language specifications
│   ├── guide/               # User guides
│   ├── design/              # Design documents
│   └── report/              # Session reports
│
└── verification/             # Lean 4 formal verification
```

---

## Development

### Building

```bash
# Debug build
simple build

# Release build
simple build --release

# With GPU support
simple build --release --features=vulkan

# Bootstrap build (minimal 9.3MB)
simple build --bootstrap
```

### Testing

**Full-suite snapshot (2026-02-14): 4,067/4,067 passing**

Simple uses a broad test strategy spanning spec tests, SDoctest, coverage, and system lanes. The counts below are from the linked 2026-02-14 report:

```bash
# All tests (4,067 tests in 17.4 seconds)
simple test

# Run specific test file
simple test path/to/spec.spl

# With verbose output
simple test --verbose

# Coverage reports
simple build coverage
```

**Test Coverage:**
- Core interpreter: 227 tests
- Compiler: 306 tests
- Standard library: 428 tests
- Applications: 142 tests
- Libraries (ML, Physics, Game): 185 tests
- Integration & Coverage: 2,779 tests

**Performance:**
- Total execution: 17.4 seconds
- Average per test: 4.3ms
- All tests deterministic and fast

See [doc/09_report/session/full_test_suite_results_2026-02-14.md](doc/09_report/session/full_test_suite_results_2026-02-14.md) for detailed test analysis.

### Code Quality

```bash
# Check before commit (fmt + lint + test)
simple build check

# Full check (includes coverage + duplication)
simple build check --full

# Format code
simple build fmt

# Lint
simple build lint
```

---

## AI Tooling (MCP, LSP, Plugin)

Simple ships with MCP servers, LSP servers, and Claude Code plugins — all written in Simple.

### Install Simple MCP Server

The Simple MCP server exposes repo-native tools for code diagnostics, VCS, build, test, debug, and related workflows. For current registration details, use the repo scripts and guide docs rather than relying on hardcoded counts here.

```bash
# From a repo checkout — register with Claude Code
claude mcp add simple-mcp -- \
  /absolute/path/to/simple/bin/release/simple \
  /absolute/path/to/simple/src/app/mcp/main.spl

# Or use the project .mcp.json (auto-detected by Claude Code)
sh config/mcp/install.shs
```

### Install Simple MCP Plugin

The `simple-mcp` Claude plugin is a repo-checkout plugin. Install it from a
Simple repository checkout; it is not a standalone portable runtime bundle.

```bash
claude plugin marketplace add tools/claude-plugin/marketplace
claude plugin install simple-mcp@simple-local
```

The plugin launches `bin/simple_mcp_server` from the repository root.

### Install Simple LSP Plugin

The Simple language server provides completions, hover, go-to-definition, diagnostics, and semantic tokens for `.spl` / `.shs` files.

```bash
# From a repo checkout
claude plugin marketplace add tools/claude-plugin/marketplace
claude plugin install simple-lsp@simple-local
```

**Binary full path:** `bin/release/simple run src/app/lsp/main.spl`

### Install Both (Quick Setup)

```bash
cd /path/to/simple

# 1. MCP server
sh config/mcp/install.shs

# 2. LSP plugin
claude plugin marketplace add tools/claude-plugin/marketplace
claude plugin install simple-lsp@simple-local
```

### Prompt Examples

Once the MCP server and LSP plugin are installed, try these prompts in Claude Code:

```
> "Run the linter on src/app/cli/main.spl and fix any warnings"

> "Show me all unused variables in the compiler frontend"

> "Run the unit tests for the SDN parser"

> "Build the project in release mode and show the result"

> "What does the function `parse_expression` in the parser do?"

> "Find all TODO items in the codebase"

> "Check the doc coverage for the standard library"

> "Debug why test/unit/lib/common/value_spec.spl is failing"
```

---

## Editor Plugins

### VSCode Extension

Full-featured extension with Tree-sitter highlighting, LSP integration, and math block support.

```bash
cd src/app/vscode_extension
npm install && npm run compile && npm run package
code --install-extension simple-language-0.1.0.vsix
```

**Key features:**
- Semantic syntax highlighting (Tree-sitter powered)
- LSP: completions, hover, go-to-definition, diagnostics
- Math block highlighting for `m{}`, `loss{}`, `nograd{}` with nested brace support
- Test CodeLens: "Run Test/File/Doctest" gutter arrows on `describe`/`it`/`context`/`sdoctest` blocks
- AI-powered completions and chat (requires GitHub Copilot)

See [`src/app/vscode_extension/README.md`](src/app/vscode_extension/README.md) for full documentation.

### Neovim Plugin

```lua
-- lazy.nvim
{ "nicholasgasior/simple.nvim", ft = "simple", opts = {} }

-- Or from project checkout
vim.opt.rtp:prepend("/path/to/simple/src/app/nvim_plugin")
require("simple").setup()
```

**Key features:**
- LSP integration with auto-detection
- Math block conceal with inline Unicode preview (`frac(1,2)` -> `(1)/(2)`, `alpha` -> `α`, `sqrt(x)` -> `√(x)`)
- Test lens: "Run" virtual text beside test blocks
- Tree-sitter queries (highlights, folds, text objects, injections)
- Brief view (fold to signatures)

See [`src/app/nvim_plugin/README.md`](src/app/nvim_plugin/README.md) for full documentation.

---

## TRACE32 Tools

MCP servers, CMM language server, and CLI tools for [Lauterbach TRACE32](https://www.lauterbach.com/en/) debuggers. See [`examples/10_tooling/trace32_tools/README.md`](examples/10_tooling/trace32_tools/README.md) for full documentation.

The repo-managed container flow is headless and uses `t32mciserver`. It does
not ship bundled TRACE32 GUI compatibility libraries; vendor runtime files must
come from your local `/opt/t32` installation.

Primary lifecycle wrapper:

```bash
scripts/t32q.shs build
scripts/t32q.shs on
scripts/t32q.shs wait
scripts/t32q.shs ping
scripts/t32q.shs reopen
scripts/t32q.shs off
```

GUI container reopen path:

```bash
scripts/t32q.shs gui-on
scripts/t32q.shs gui-reopen
scripts/t32q.shs off
```

`gui-on` uses the Docker/Podman TRACE32 GUI path with host X11 forwarding, so
it requires a real host X11 session (`DISPLAY`, `/tmp/.X11-unix`, and usually
`XAUTHORITY`). For quick diagnostics use:

```bash
scripts/t32q.shs doctor
```

Hello-world firmware smoke:

```bash
scripts/t32_semihost_hello.shs --board stm32wb
scripts/t32_semihost_hello.shs --board stm32h7
scripts/t32_semihost_hello.shs --board stm32wb --build-only
```

### Install T32 MCP Servers

```bash
cd /path/to/simple

# T32 MCP — controls live TRACE32 debug sessions (23 tools)
claude mcp add t32-mcp -- \
  /absolute/path/to/simple/bin/release/simple \
  /absolute/path/to/simple/examples/10_tooling/trace32_tools/t32_mcp/main.spl

# T32 LSP MCP — CMM script analysis, no hardware needed (6 tools)
claude mcp add t32-lsp-mcp -- \
  /absolute/path/to/simple/bin/release/simple \
  /absolute/path/to/simple/examples/10_tooling/trace32_tools/t32_lsp_mcp/main.spl
```

**Binary full paths:**
- T32 MCP: `bin/release/simple examples/10_tooling/trace32_tools/t32_mcp/main.spl`
- T32 LSP MCP: `bin/release/simple examples/10_tooling/trace32_tools/t32_lsp_mcp/main.spl`

### Install CMM LSP Plugin

```bash
claude plugin marketplace add tools/claude-plugin/marketplace
claude plugin install cmm-lsp@simple-local
```

**Binary full path:** `bin/release/simple examples/10_tooling/trace32_tools/cmm_lsp/mod.spl --lsp`

### T32 Prompt Examples

```
> "Parse this CMM script and check for errors: config/t32/stm32h7_gdb_start.cmm"

> "Connect to TRACE32 on localhost:20000 and read the CPU registers"

> "Show me all labels and macros defined in my CMM script"

> "Convert this GUI PRACTICE script to CLI batch mode"

> "Check if my CMM script has any undefined macros or unreachable code"

> "Set a breakpoint at main, run to it, and show local variables"

> "What TRACE32 commands are available for memory access?"

> "Auto-complete suggestions for 'Data.LOAD' in my CMM script"
```

---

## Contributing

See [CLAUDE.md](CLAUDE.md) for development guidelines and [AGENTS.md](AGENTS.md) for AI agent instructions.

**Documentation Structure:**
- **Specifications** go in [doc/06_spec/](doc/06_spec/) (what the language supports)
- **Guides** go in [doc/07_guide/](doc/07_guide/) (how to use features)
- **Research** goes in [doc/01_research/](doc/01_research/) (why/how decisions were made)
- **Plans** go in [doc/03_plan/](doc/03_plan/) (implementation roadmaps)
- **Reports** go in [doc/09_report/](doc/09_report/) (session summaries and completion reports)

---

## License

MIT License. See [LICENSE](LICENSE).

Bundled third-party runtime components and redistribution notices are listed in
[THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).

Release packages also include `THIRD_PARTY_NOTICES.md`.

---

## Resources

**Official Documentation:**
- [Documentation Hub](doc/README.md) - Entry point for the numbered docs tree
- [Language Specification](doc/06_spec/README.md) - Current spec index
- [User Guides](doc/07_guide/README.md) - Practical tutorials

**Quick References:**
- [Syntax Quick Reference](doc/07_guide/quick_reference/syntax_quick_reference.md)
- [Type System Guide](doc/07_guide/language/type_system.md)
- [GPU Computing Guide](doc/07_guide/backend/gpu_programming.md)

**Development:**
- [Architecture Overview](doc/04_architecture/overview.md)
- [Feature Documentation](doc/06_spec/feature.md)
- [Implementation Plans](doc/03_plan/README.md)
