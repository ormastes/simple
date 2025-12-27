# Simple Language

A statically typed programming language with Python-like syntax, modern safety features, and GPU computing support.

**Quick Navigation:** [Features](#key-features) | [Quick Start](#quick-start) | [Language Basics](#language-basics) | [Documentation](#documentation) | [Grammar & Spec](#grammar--specification) | [Project Structure](#project-structure)

---

## Key Features

- **Python-like syntax** - Indentation-based blocks, clean readable code
- **Static typing with inference** - Type safety without verbosity (Hindley-Milner)
- **Multiple memory modes** - GC-managed (default), manual, or reference-counted
- **Actor-based concurrency** - Safe concurrent programming with async/await
- **GPU computing** - Cross-platform Vulkan backend for GPU kernels and SIMD
- **Pattern matching** - Exhaustiveness checking with strong enums
- **Contracts** - Pre/postconditions, invariants (DbC - Design by Contract)
- **Macros** - Hygienic compile-time metaprogramming
- **SMF binary format** - Compile once, run anywhere

---

## Quick Start

### Installation

```bash
# Build from source
cargo build --release

# Binary location
./target/release/simple

# (Optional) Add to PATH
export PATH="$PWD/target/release:$PATH"
```

### Build with GPU Support

```bash
cargo build --release --features vulkan
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
>>> let x = 10
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
# Variables are mutable by default
x = 10
let y = 20          # 'let' is optional
const PI = 3.14159  # Immutable constant

# Type annotations (optional due to inference)
let count: i64 = 100

# Basic types
let a: i32 = 42
let pi: f64 = 3.14159
let flag: bool = true

# Strings with interpolation
let name = "world"
let msg = "Hello, {name}!"

# Raw strings (no interpolation)
let path = 'C:\Users\name'
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
let sum = add(1, 2)
greet("Alice")

# Lambdas use backslash
let double = \x: x * 2
let evens = nums.filter \x: x % 2 == 0
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

let p = Point(x: 1.0, y: 2.0)

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

let alice = Person(name: "Alice", age: 30)
alice.greet()
```

### Collections

```simple
# Arrays
let nums = [1, 2, 3, 4, 5]
let first = nums[0]

# Dictionaries
let scores = {"alice": 100, "bob": 85}
let alice_score = scores["alice"]

# Tuples
let pair = (1, "hello")
let (num, text) = pair
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

### Functional Update Operator (`->`)

```simple
# The -> operator calls a method and assigns result back
let mut data = load_data()
data->normalize()        # data = data.normalize()
data->filter(min: 0)     # data = data.filter(min: 0)

# Chaining
data->normalize()->filter(min: 0)->save("out.txt")
```

### GPU Computing

```simple
import std.gpu

# GPU kernel - runs on device
#[gpu]
fn vector_add_kernel(a: []f32, b: []f32, result: []f32):
    idx = gpu.global_id(0)
    if idx < len(result):
        result[idx] = a[idx] + b[idx]

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
cargo build

# Release build
cargo build --release

# With GPU support
cargo build --release --features vulkan

# Run all tests
cargo test --workspace

# Run stdlib tests
cargo test -p simple-driver simple_stdlib
```

### Testing

Simple uses a comprehensive test strategy with multiple levels:

```bash
# Unit tests (631+ tests)
make test-unit

# Integration tests
make test-it

# System tests
make test-system

# All tests
make test

# Coverage reports
make coverage
```

See [doc/guides/test.md](doc/guides/test.md) for complete testing documentation.

### Code Quality

```bash
# Check before commit (fmt + lint + test)
make check

# Full check (includes coverage + duplication)
make check-full

# Format code
make fmt

# Lint
make lint

# Detect code duplication
make duplication
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
