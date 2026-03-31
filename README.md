# Simple Language

[![Production Ready](https://img.shields.io/badge/status-production%20ready-brightgreen)](doc/archive/release/PRODUCTION_READY_SUMMARY.md)
[![Tests](https://img.shields.io/badge/tests-4067%2F4067%20passing-brightgreen)](doc/09_report/session/full_test_suite_results_2026-02-14.md)
[![LLVM Cross](https://github.com/simple-lang/simple/actions/workflows/simple-llvm-cross.yml/badge.svg)](.github/workflows/simple-llvm-cross.yml)
[![License](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE)

Simple is a self-hosted language and toolchain that combines a readable Python-like surface with compiler-integrated testing, documentation, architecture rules, and baremetal-oriented execution paths.

The repo is unusually broad: language, compiler, interpreter, loader, test runner, doc generation, traceability tooling, SDN-backed project databases, editor tooling, and hardware-oriented test flows all live together.

**Quick Navigation:** [Distinctive Features](#distinctive-features) | [Feature Status](#feature-status-highlights) | [Quick Start](#quick-start) | [Language Basics](#language-basics) | [Examples](#examples) | [Documentation](#documentation)

---

## Distinctive Features

- **Self-hosted staged toolchain**: real source layers for frontend, types, borrow checking, backend, driver, interpreter, and loader.
- **Verification-first workflow**: SSpec BDD tests, SDoctest executable docs, coverage, traceability checks, and generated spec markdown all ship in-tree.
- **MDSOC architecture support**: virtual capsules, capsule manifests, and architecture-oriented repo structure are first-class concepts.
- **Parser-friendly macro system**: compiler-integrated macro definitions, validation, and hygiene instead of editor-hostile text substitution.
- **Math DSL blocks**: `m{}`, `loss{}`, and `nograd{}` parse and evaluate as dedicated math-oriented syntax, with pretty/LaTeX rendering support.
- **SDN-backed project databases**: the repo uses textual SDN stores for tests, todos, dashboards, and other project metadata.
- **Baremetal-friendly execution model**: in-tree support for baremetal builds, semihosting lanes, QEMU/GHDL flows, host-aware remote baremetal plumbing, and real CH32/STM adapter-backed lanes.
- **Multiple execution paths**: interpreter, loader, native/LLVM-oriented compilation paths, and SMF/module-loading infrastructure coexist in one repo.
- **Tooling-aware language rules**: Tree-sitter integration, primitive-public-API linting, traceability tooling, and language statistics are part of the platform story.
- **UI test sharing**: the UI test client is designed to exercise both web UI backends and the TUI web proxy through one HTTP-oriented test surface.

## Feature Status Highlights

Implemented and safe to advertise:
- SSpec, SDoctest, coverage, traceability checks, and generated spec docs
- MDSOC manifests and architecture-focused project structure
- Tree-sitter outline/query tooling
- SDN project/test/todo databases
- Primitive public API linting
- Borrow-checking infrastructure
- Watch mode / auto-build support
- mmap-backed loader primitives and executable-memory support
- Baremetal build/test plumbing, remote baremetal mode parsing, and adapter-backed CH32 composite execution

Implemented but should be described carefully:
- `loss{}` / `nograd{}` and math-block rendering work, but deeper DL automation around them is still evolving
- LLVM support is real, but some flows still depend on external LLVM tools
- GC and no-GC families both exist, but their completeness is not uniform across every toolchain path
- UI sharing exists through test surfaces and multiple frontends, but not as a single finished “one UI layer everywhere” claim

Partial or experimental:
- [todo] AOP support has a verified baseline: Simple-side proceed enforcement, MIR weaving helpers, and Rust-side runtime `init(...)` interception with `@inject` are covered. The broader DI/AOP authoring surface should still be treated as in progress. Current state: [doc/01_research/local/aop.md](doc/01_research/local/aop.md)
- [todo] Remote baremetal execution is real but still lane-dependent. Stable RV32 ELF/shared-workload proof, CH32 composite-runner execution, and runtime/readiness checks are implemented; full repo-wide “all hardware lanes green” status is still host-dependent. Current state: [doc/03_plan/remote_baremetal_remaining_without_trace32_2026-03-24.md](doc/03_plan/remote_baremetal_remaining_without_trace32_2026-03-24.md)
- [todo] Loader/JIT instantiation still has stubbed pieces. Current state: [doc/03_plan/loader_linker_object_provider_refactor_2026-02-18.md](doc/03_plan/loader_linker_object_provider_refactor_2026-02-18.md)
- [todo] VHDL backend code generation exists, but should still be treated as experimental. Current state: [doc/03_plan/vhdl_backend_riscv_remote_interpreter_plan_2026-03-23.md](doc/03_plan/vhdl_backend_riscv_remote_interpreter_plan_2026-03-23.md)
- [todo] C/C++ bidirectional interop has substantial SFFI infrastructure, but not enough evidence to present it as fully complete. Current state: [doc/05_design/sffi_bidirectional_interop.md](doc/05_design/sffi_bidirectional_interop.md)
- [todo] Lean generation, artifact inventory, and proof-checking commands exist, but the supported end-to-end formal verification workflow is still partial. Current state: [doc/03_plan/lean_verification_implementation.md](doc/03_plan/lean_verification_implementation.md)

See [doc/report/unique_features.md](doc/report/unique_features.md) for the evidence-backed audit.

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

See [doc/build/bootstrap_multi_platform.md](doc/build/bootstrap_multi_platform.md) and [plan_codex_bootstrap.md](plan_codex_bootstrap.md) for the current bootstrap flow.

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

Unified predicate grammar for cross-cutting concerns:

```simple
# Pointcut expression syntax: pc{...}
# Applies logging to all service methods
on pc{ execution(services.**.*(..)) } use LoggingInterceptor

# Architecture rules - enforce layer dependencies
forbid pc{ hal.** } -> pc{ services.** }  # HAL cannot depend on services
allow  pc{ services.** } -> pc{ hal.** }  # Services can use HAL

# Dependency Injection with predicates
bind on pc{ attr(Repository) } -> PostgresRepository
  when profile("prod")

bind on pc{ attr(Repository) } -> MockRepository
  when profile("test")
```

Current repo status: compile-time weaving is the primary AOP path. The verified runtime slice currently covers `proceed()` enforcement and runtime `init(...)` interception with `@inject`, but broader DI/AOP authoring should still be treated as in progress.

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

### Doctest

Executable examples in docstrings — tests that serve as documentation:

```simple
## Computes factorial of n
##
## Example: factorial(5) returns 120
## Example: factorial(0) returns 1
fn factorial(n: i64) -> i64:
    if n <= 1: return 1
    n * factorial(n - 1)

print factorial(5)   # 120
print factorial(0)   # 1
```

**Data structures with doc comments:**

```simple
## Stack data structure with LIFO semantics
##
## Usage:
##     var s = Stack(items: [])
##     s.items.push(1)
##     s.items.push(2)
##     print s.items.len()  # 2
struct Stack:
    items: [i64]

var s = Stack(items: [])
s.items.push(1)
s.items.push(2)
s.items.push(3)
print s.items.len()  # 3
```

**Planned interactive doctest syntax** (under development):

```text
# Future syntax — not yet implemented:
"""
>>> factorial(5)
120
>>> generate_uuid()
"........-....-....-....-............"
"""
```

Run doctests:
```bash
simple doctest src/math.spl      # Run doctests in file
simple doctest doc/tutorial.md   # Run doctests in markdown
simple test --doctest            # Run all doctests
simple test --doctest --tag slow # Run only slow-tagged doctests
```

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
| **Language Spec** | Complete language specification | [doc/spec/README.md](doc/spec/README.md) |
| **Grammar** | Parser grammar and syntax rules | [doc/spec/parser/](doc/spec/parser/) |
| **Guides** | Practical how-to guides | [doc/guides/README.md](doc/guides/README.md) |
| **Plans** | Implementation roadmap | [doc/plans/README.md](doc/plans/README.md) |
| **Research** | Design explorations | [doc/research/README.md](doc/research/README.md) |
| **Architecture** | System design principles | [doc/architecture/](doc/architecture/) |
| **Features** | Feature catalog | [doc/features/feature.md](doc/features/feature.md) |
| **Status** | Implementation tracking | [doc/status/](doc/status/) |
| **Deep Learning** | Neural networks & GPU computing | [doc/guide/deep_learning_guide.md](doc/guide/deep_learning_guide.md) |

### Core Documentation

**Getting Started:**
- [Language Specification Index](doc/spec/README.md) - Complete spec organized by topic
- [Syntax Specification](doc/spec/syntax.md) - Lexical structure, literals, operators
- [Type System](doc/spec/types.md) - Type system, mutability, inference
- [Test Policy](doc/guides/test.md) - Testing framework and best practices

**Language Reference:**
- [Core Language](doc/spec/README.md#core-language) - Syntax, types, data structures, functions
- [Advanced Features](doc/spec/README.md#advanced-features) - Concurrency, macros, contracts
- [Standard Library](doc/spec/stdlib.md) - Standard library specification

**GPU Computing:**
- [Deep Learning Guide](doc/guide/deep_learning_guide.md) - **Comprehensive DL guide** (Pure Simple, PyTorch, CUDA)
- [Vulkan User Guide](doc/guides/vulkan_backend.md) - Getting started with GPU kernels
- [GPU & SIMD Spec](doc/spec/gpu_simd/README.md) - GPU compute and SIMD specification
- [Vulkan Architecture](doc/architecture/vulkan_backend.md) - Implementation details

**Development:**
- [Module System](doc/spec/modules.md) - Import/export, packages, __init__.spl
- [Testing Framework](doc/spec/testing/testing_bdd_framework.md) - BDD testing with matchers
- [Build System](doc/guides/test.md) - Building and testing Simple projects

**Advanced Features:**
- [Macro System](doc/spec/macro.md) - Contract-first LL(1) macros
- [AOP & Unified Predicates](doc/01_research/local/aop.md) - Aspect-oriented programming and current implementation status
- [SDN Format](doc/spec/sdn.md) - Simple Data Notation specification
- [Doctest](doc/spec/testing/sdoctest.md) - Documentation testing
- [Feature Documentation](doc/features/feature.md) - BDD-generated feature docs

---

## Examples

### Deep Learning Examples

Simple provides 17 deep learning examples across 4 categories:

**Pure Simple Neural Networks (7 examples - 100% working):**
```bash
# XOR neural network training
bin/simple examples/pure_nn/xor_training_example.spl

# Linear regression (learns y = 2x + 1)
bin/simple examples/pure_nn/simple_regression.spl

# Iris flower classification
bin/simple examples/pure_nn/iris_classification.spl
```

**MedGemma Korean Fine-Tuning (3 phases - 100% working):**
```bash
# Progressive LoRA training to prevent catastrophic forgetting
bin/simple examples/medgemma_korean/run_all.spl
```

**CUDA Programming (1 example - 100% working):**
```bash
# Direct CUDA C API - multi-GPU, streams, events
bin/simple examples/cuda/basic.spl
```

**See [Deep Learning Guide](doc/guide/deep_learning_guide.md) for complete documentation.**

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

Generated docs appear in `doc/features/{category}/` folders with living documentation that stays in sync with the implementation.

---

## Grammar & Specification

### Language Grammar

The Simple language grammar is formally specified in the parser documentation:

**Grammar Documents:**
- [Parser Overview](doc/spec/parser/overview.md) - Parser architecture and design
- [Grammar Definitions](doc/spec/parser/lexer_parser_grammar_definitions.md) - Top-level definitions
- [Grammar Expressions](doc/spec/parser/lexer_parser_grammar_expressions.md) - Expression grammar
- [Lexer & Scanner](doc/spec/parser/lexer_parser_scanner.md) - Tokenization rules
- [Complete Grammar](doc/spec/parser/lexer_parser_grammar.md) - Full BNF-style grammar

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

The complete language specification is organized in [doc/spec/](doc/spec/):

**Core Language (9 specs):**
- [Syntax](doc/spec/syntax.md) - Lexical structure, operators
- [Types](doc/spec/types.md) - Type system, mutability
- [Data Structures](doc/spec/data_structures.md) - Structs, classes, enums
- [Functions](doc/spec/functions.md) - Functions, pattern matching
- [Traits](doc/spec/traits.md) - Traits and implementations
- [Memory](doc/spec/memory.md) - Ownership, borrowing
- [Modules](doc/spec/modules.md) - Import/export system
- [Units](doc/spec/units.md) - Semantic unit types
- [Primitive as Object](doc/spec/primitive_as_obj.md) - Primitive methods

**Advanced Features (8 specs):**
- [Concurrency](doc/spec/concurrency.md) - Actors, async/await
- [Metaprogramming](doc/spec/metaprogramming.md) - Macros, decorators
- [Macro System](doc/spec/macro.md) - Advanced macros
- [Contracts](doc/spec/invariant.md) - Pre/postconditions
- [Capability Effects](doc/spec/capability_effects.md) - Reference capabilities
- [FFI & ABI](doc/spec/ffi_abi.md) - Foreign function interface
- [Standard Library](doc/spec/stdlib.md) - Stdlib organization
- [File I/O](doc/spec/file_io.md) - File operations

**Testing & Tooling:**
- [BDD Testing](doc/spec/testing/testing_bdd_framework.md) - BDD framework, matchers
- [Formatter](doc/spec/tooling/formatter.md) - Code formatting
- [Linting](doc/spec/tooling/formatting_lints.md) - Linter rules

**GPU & Graphics:**
- [GPU & SIMD](doc/spec/gpu_simd/README.md) - GPU compute specification
- [3D Graphics](doc/spec/graphics_3d/README.md) - 3D rendering

See [doc/spec/README.md](doc/spec/README.md) for the complete specification index with status indicators.

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

**Production Ready Test Suite: 4,067/4,067 passing (100%)**

Simple uses a comprehensive test strategy with 100% pass rate:

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

See [doc/session/full_test_suite_results_2026-02-14.md](doc/session/full_test_suite_results_2026-02-14.md) for detailed test analysis.

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

The Simple MCP server currently exposes 99 tools for code diagnostics, VCS, build, test, debug, and more, plus 3 resources and 2 prompts.

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

## TRACE32 Tools

MCP servers, CMM language server, and CLI tools for [Lauterbach TRACE32](https://www.lauterbach.com/en/) debuggers. See [`examples/10_tooling/trace32_tools/README.md`](examples/10_tooling/trace32_tools/README.md) for full documentation.

The repo-managed container flow is headless and uses `t32mciserver`. It does
not ship bundled TRACE32 GUI compatibility libraries; vendor runtime files must
come from your local `/opt/t32` installation.

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
- **Specifications** go in [doc/spec/](doc/spec/) (what the language supports)
- **Guides** go in [doc/guides/](doc/guides/) (how to use features)
- **Research** goes in [doc/research/](doc/research/) (why/how decisions were made)
- **Plans** go in [doc/plans/](doc/plans/) (implementation roadmaps)
- **Reports** go in [doc/report/](doc/report/) (session summaries, completion reports)

---

## License

MIT License. See [LICENSE](LICENSE).

Bundled third-party runtime components and redistribution notices are listed in
[THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).

Release packages also include `THIRD_PARTY_NOTICES.md`.

---

## Resources

**Official Documentation:**
- [Language Specification](doc/spec/README.md) - Complete spec index
- [Grammar Reference](doc/spec/parser/) - Parser grammar
- [User Guides](doc/guides/README.md) - Practical tutorials

**Quick References:**
- [Syntax Quick Reference](doc/spec/syntax.md#quick-reference)
- [Type System Guide](doc/spec/types.md)
- [GPU Computing Guide](doc/guides/vulkan_backend.md)

**Development:**
- [Architecture Overview](doc/architecture/overview.md)
- [Feature Roadmap](doc/features/feature.md)
- [Implementation Plans](doc/plans/README.md)
