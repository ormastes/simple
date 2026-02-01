# Simple Language

A statically typed programming language with Python-like syntax, modern safety features, and GPU computing support.

**Quick Navigation:** [Features](#key-features) | [Quick Start](#quick-start) | [Language Basics](#language-basics) | [Examples](#examples) | [BDD Docs](#bdd-feature-documentation) | [Documentation](#documentation) | [Grammar & Spec](#grammar--specification) | [Project Structure](#project-structure)

---

## Key Features

- **Self-Hosting Build System** - Complete build system written in Simple itself
- **Python-like syntax** - Indentation-based blocks, clean readable code
- **Static typing with inference** - Type safety without verbosity (Hindley-Milner)
- **Unit types** - Type-safe postfix literals (`10_cm`, `200_kmph`, `42_uid`)
- **Multiple memory modes** - GC-managed (default), manual, or reference-counted
- **Actor-based concurrency** - Safe concurrent programming with async/await
- **GPU computing** - Cross-platform Vulkan backend with `this.index()` / `gpu.global_id()`
- **Pattern matching** - Exhaustiveness checking with strong enums
- **Contracts** - Pre/postconditions, invariants (DbC - Design by Contract)
- **Parser-friendly macros** - Contract-first LL(1) macros with IDE support
- **AOP & Unified Predicates** - Aspect-oriented programming, DI, mocking, architecture rules
- **SDN configuration** - Simple Data Notation for human-readable config files
- **Doctest** - Executable examples in docstrings (`>>> prompt` style)
- **BDD Feature Docs** - Living documentation generated from passing tests
- **SMF binary format** - Compile once, run anywhere

---

## Quick Start

### Installation

```bash
# Build from source (using Simple's self-hosting build system)
simple build --release

# Or bootstrap from source (first-time)
cd rust && cargo build --release

# Binary location
./rust/target/release/simple_runtime

# (Optional) Add to PATH
export PATH="$PWD/bin/wrappers:$PATH"
```

### Build with GPU Support

```bash
simple build --release --features=vulkan
# Or: cd rust && cargo build --release --features vulkan
```

### Your First Program

```simple
# hello.spl
main = 0  # Entry point, returns exit code
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
>>> val x = 10
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

```simple
# Variables - immutable (val) or mutable (var)
val x = 10          # Immutable (preferred)
var y = 20          # Mutable (when needed)
val PI = 3.14159    # Immutable constant

# Type annotations (optional due to inference)
val count: i64 = 100

# Basic types
vala: i32 = 42
valpi: f64 = 3.14159
valflag: bool = true

# Strings with interpolation
valname = "world"
valmsg = "Hello, {name}!"

# Raw strings (no interpolation)
valpath = 'C:\Users\name'
```

### Control Flow

```simple
# If/else with indentation
if x > 0:
    print "positive"
elif x < 0:
    print "negative"
else:
    print "zero"

# Loops
for i in 0..10:
    print i

while x > 0:
    x = x - 1

# Infinite loop with break/continue
loop:
    if done:
        break
    continue
```

### Functions

```simple
fn add(a: i64, b: i64) -> i64:
    return a + b

fn greet(name: str):
    print "Hello, {name}!"

# Call functions
valsum = add(1, 2)
greet("Alice")

# Lambdas use backslash
valdouble = \x: x * 2
valevens = nums.filter \x: x % 2 == 0
```

### Structs & Classes

```simple
# Structs (value types, immutable by default)
struct Point:
    x: f64
    y: f64

# Mutable struct
mut struct Cursor:
    x: f64
    y: f64

valp = Point(x: 1.0, y: 2.0)

# Classes (reference types, mutable by default)
class Person:
    name: str
    age: i32

    fn greet(self):
        print "Hi, I'm {self.name}"

# Immutable class
immut class Color:
    red: u8
    green: u8
    blue: u8

valalice = Person(name: "Alice", age: 30)
alice.greet()
```

### Collections

```simple
# Arrays
valnums = [1, 2, 3, 4, 5]
valfirst = nums[0]

# Dictionaries
valscores = {"alice": 100, "bob": 85}
valalice_score = scores["alice"]

# Tuples
valpair = (1, "hello")
val(num, text) = pair
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
valheight = 175_cm              # Length type
valwidth = 10_cm + 5_mm         # Auto-converts to same base
valspeed = 200_kmph             # Velocity type
valdistance = 42_km             # Length type

# Type safety - compile error:
# valbad = height + speed       # Error: can't add Length + Velocity

# Semantic IDs prevent mix-ups
valuser = 42_uid                # UserId
valorder = 100_oid              # OrderId
# valwrong: UserId = 100_oid    # Error: OrderId ≠ UserId

# Computed units
valtravel_time = distance / speed    # Returns Time type
print("ETA: {travel_time.to_min()} minutes")
```

### Pattern Matching

```simple
enum Shape:
    Circle(radius: f64)
    Rectangle(width: f64, height: f64)

fn area(s: Shape) -> f64:
    match s:
        Circle(r):
            return 3.14159 * r * r
        Rectangle(w, h):
            return w * h
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
      return start + step

# Usage - IDE knows about UserCounter before expansion
class Demo:
  define_counter!("User")

  fn run(self) -> Int:
    return self.UserCounter(10)  # Autocomplete works!
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
valnums = vec![1, 2, 3, 4, 5]       # Create vector
valformatted = format!("x={x}")     # Format string without printing

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
        return v[i]

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

Executable examples in docstrings - tests that serve as documentation:

```simple
"""
Computes factorial of n

Examples:
```sdoctest
>>> factorial(5)
120
>>> factorial(0)
1
>>> factorial(-1)
Error: ValueError
```
"""
fn factorial(n: Int) -> Int:
    if n < 0: raise ValueError("negative input")
    if n <= 1: return 1
    return n * factorial(n - 1)
```

**Multi-line examples and setup/teardown:**

```simple
"""
Stack data structure with LIFO semantics

Setup:
```sdoctest
>>> stack = Stack.new()
```

Examples:
```sdoctest
>>> stack.push(1)
>>> stack.push(2)
>>> stack.push(3)
>>> stack.pop()
3
>>> stack.pop()
2
>>> stack.size()
1
```

Error handling:
```sdoctest
>>> empty = Stack.new()
>>> empty.pop()
Error: EmptyStackError
```
"""
class Stack:
    # ...
```

**Wildcard matching for non-deterministic output:**

```simple
"""
Generate unique identifiers

```sdoctest
>>> generate_uuid()
"........-....-....-....-............"
>>> get_timestamp()
1702......
>>> random_int(1, 100)
..
```
"""
fn generate_uuid() -> String:
    # ...
```

**Doctest in Markdown files:**

````markdown
# Tutorial: Getting Started

Create your first Simple program:

```sdoctest
>>> val x = 10
>>> valy = 20
>>> x + y
30
>>> "Result: {x + y}"
"Result: 30"
```
````

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
    vali = this.index()             # Global linear index (same as gpu.global_id())
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
    valrow = gpu.global_id(0)       # First dimension
    valcol = gpu.global_id(1)       # Second dimension

    # Thread group (workgroup) info
    vallocal_row = gpu.local_id(0)  # Index within workgroup
    valgroup_row = gpu.group_id(0)  # Workgroup index

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
- [Vulkan User Guide](doc/guides/vulkan_backend.md) - Getting started with GPU kernels
- [GPU & SIMD Spec](doc/spec/gpu_simd/README.md) - GPU compute and SIMD specification
- [Vulkan Architecture](doc/architecture/vulkan_backend.md) - Implementation details

**Development:**
- [Module System](doc/spec/modules.md) - Import/export, packages, __init__.spl
- [Testing Framework](doc/spec/testing/testing_bdd_framework.md) - BDD testing with matchers
- [Build System](doc/guides/test.md) - Building and testing Simple projects

**Advanced Features:**
- [Macro System](doc/spec/macro.md) - Contract-first LL(1) macros
- [AOP & Unified Predicates](doc/research/aop.md) - Aspect-oriented programming
- [SDN Format](doc/spec/sdn.md) - Simple Data Notation specification
- [Doctest](doc/spec/testing/sdoctest.md) - Documentation testing
- [Feature Documentation](doc/features/feature.md) - BDD-generated feature docs

---

## Examples

The `simple/std_lib/examples/` directory contains working examples:

| Example | Description |
|---------|-------------|
| `cli_demo.spl` | Command-line argument parsing |
| `file_async_basic.spl` | Async file I/O operations |
| `ui_todo_app.spl` | Cross-platform UI application |
| `vulkan_triangle.spl` | GPU rendering with Vulkan |
| `async_tcp_echo_server.spl` | Async TCP networking |

Run an example:
```bash
./target/debug/simple simple/std_lib/examples/cli_demo.spl
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
├── src/                      # Rust compiler implementation
│   ├── parser/               # Lexer and parser
│   ├── type/                 # Type checker with Hindley-Milner inference
│   ├── compiler/             # HIR, MIR, and codegen
│   │   ├── hir/              # High-level IR (type-checked)
│   │   ├── mir/              # Mid-level IR (50+ instructions)
│   │   ├── codegen/          # Cranelift backend
│   │   └── interpreter/      # Fallback interpreter
│   ├── loader/               # SMF binary loader
│   ├── runtime/              # GC and runtime support
│   │   ├── value/            # Runtime value system
│   │   └── memory/           # Memory management (GC, no-GC)
│   └── driver/               # CLI and execution
│
├── simple/                   # Simple language workspace
│   ├── app/                  # Self-hosted applications (formatter, linter, LSP)
│   ├── std_lib/              # Standard library (written in Simple)
│   │   ├── src/              # Library source (.spl files)
│   │   └── test/             # Library tests (unit, system, integration)
│   └── bin_simple/           # Compiled Simple executables
│
├── doc/                      # Documentation (349+ files)
│   ├── spec/                 # Language specifications (50 files)
│   │   ├── README.md         # Comprehensive spec index
│   │   ├── parser/           # Grammar documentation (6 files)
│   │   ├── testing/          # Test framework specs (6 files)
│   │   ├── tooling/          # Development tool specs (5 files)
│   │   ├── gpu_simd/         # GPU & SIMD specs (13 files)
│   │   └── graphics_3d/      # 3D graphics specs
│   ├── guides/               # Practical how-to guides (15 files)
│   │   └── README.md         # Guide index by purpose
│   ├── plans/                # Implementation roadmap (55 files)
│   │   └── README.md         # Plan index with status
│   ├── research/             # Design explorations (43 files)
│   │   └── README.md         # Research index by topic
│   ├── architecture/         # System design principles
│   ├── features/             # Feature catalog and history
│   ├── status/               # Implementation tracking (69 files)
│   └── report/               # Session reports and summaries
│
├── verification/             # Lean 4 formal verification
│   ├── memory_model_drf/     # SC-DRF memory model
│   └── memory_capabilities/  # Reference capability verification
│
├── tests/                    # Integration and system tests
└── examples/                 # Example programs
    └── gpu/vulkan/           # GPU computing examples
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

# Run all Rust tests
simple build rust test

# Run stdlib tests
simple build rust test -p simple-driver simple_stdlib
```

### Testing

Simple uses a comprehensive test strategy with multiple levels:

```bash
# All tests (Rust + Simple)
simple build test

# Rust tests only
simple build rust test

# Rust doc-tests
simple build rust test --doc

# Coverage reports
simple build coverage
```

See [doc/guides/test.md](doc/guides/test.md) for complete testing documentation.

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

MIT License

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
