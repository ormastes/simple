# Simple Language

A statically typed programming language with Python-like syntax and modern safety features.

## Features

- **Python-like syntax** - Indentation-based blocks, clean readable code
- **Static typing with inference** - Type safety without verbosity
- **Multiple memory modes** - GC-managed (default), manual, or reference-counted
- **Actor-based concurrency** - Safe concurrent programming
- **SMF binary format** - Compile once, run anywhere

## Quick Start

### Build

```bash
cargo build --release
```

### Run

```bash
# Interactive REPL
simple

# Run a source file
simple hello.spl

# Run compiled binary
simple hello.smf

# Run code directly
simple -c "42"
simple -c "let x = 10\nmain = x * 5"
```

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
# Start interactive REPL
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
# Exit code: 42

# Compile to binary
simple compile hello.spl
simple hello.smf  # Run the compiled binary

# Watch mode (auto-recompile on changes)
simple watch app.spl
```

## Language Basics

### Hello World

```simple
# main is the entry point, returns an integer exit code
main = 0
```

### Variables

```simple
# Variables are mutable by default
x = 10
let y = 20          # 'let' is optional
const PI = 3.14159  # Immutable constant

# Type annotations (optional due to inference)
let count: i64 = 100
```

### Basic Types

```simple
# Integers
let a: i32 = 42
let b: i64 = 1_000_000

# Floats
let pi: f64 = 3.14159

# Boolean
let flag: bool = true

# String (with interpolation)
let name = "world"
let msg = "Hello, {name}!"

# Raw string (no interpolation)
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

# Loop with break/continue
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
```

### Structs (Value Types)

```simple
# Immutable by default
struct Point:
    x: f64
    y: f64

# Mutable struct
mut struct Cursor:
    x: f64
    y: f64

let p = Point(x: 1.0, y: 2.0)
```

### Classes (Reference Types)

```simple
# Mutable by default
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

### Lambdas

```simple
# Lambda syntax uses backslash
let double = \x: x * 2
let add = \a, b: a + b

# With collections
let evens = nums.filter \x: x % 2 == 0
let doubled = nums.map \x: x * 2
```

### Functional Update (`->`)

```simple
# The -> operator calls a method and assigns result back
let mut data = load_data()
data->normalize()        # data = data.normalize()
data->filter(min: 0)     # data = data.filter(min: 0)

# Chaining
data->normalize()->filter(min: 0)->save("out.txt")
```

## Project Structure

```
simple/
├── src/
│   ├── parser/      # Lexer and parser
│   ├── type/        # Type checker with inference
│   ├── compiler/    # HIR, MIR, and codegen
│   ├── loader/      # SMF binary loader
│   ├── runtime/     # GC and runtime support
│   └── driver/      # CLI and execution
├── doc/             # Documentation
│   ├── architecture/         # High-level system architecture notes
│   ├── codegen/              # Backend implementation details
│   ├── design/               # Design explorations
│   ├── examples/             # Sample code
│   ├── features/             # Feature roadmap and history
│   ├── formal_verification/  # Lean 4 formalization work
│   ├── guides/               # Operational and process guidance
│   ├── plans/                # Detailed implementation plans
│   ├── research/             # Research notes
│   ├── spec/                 # Language and compiler specs
│   └── status/               # Feature implementation tracking
└── tests/           # Test suites
```

## Documentation

- [Language Specification](doc/spec/language.md)
- [Architecture Overview](doc/architecture/overview.md)
- [Feature Roadmap](doc/features/feature.md)
- [Test Policy](doc/guides/test.md)

## License

MIT License
