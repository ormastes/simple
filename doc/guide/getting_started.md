# Getting Started with Simple

This guide will help you install Simple and write your first programs.

---

## Installation

### Quick Install (Recommended)

Download the pre-compiled release for your platform:

**Linux x86_64:**
```bash
wget https://github.com/simple-lang/simple/releases/download/v0.5.0/simple-0.5.0-linux-x86_64.tar.gz
tar -xzf simple-0.5.0-linux-x86_64.tar.gz
cd simple-0.5.0
export PATH="$PWD/bin:$PATH"
```

**macOS ARM64 (Apple Silicon):**
```bash
curl -LO https://github.com/simple-lang/simple/releases/download/v0.5.0/simple-0.5.0-darwin-aarch64.tar.gz
tar -xzf simple-0.5.0-darwin-aarch64.tar.gz
cd simple-0.5.0
export PATH="$PWD/bin:$PATH"
```

**macOS x86_64 (Intel):**
```bash
curl -LO https://github.com/simple-lang/simple/releases/download/v0.5.0/simple-0.5.0-darwin-x86_64.tar.gz
tar -xzf simple-0.5.0-darwin-x86_64.tar.gz
cd simple-0.5.0
export PATH="$PWD/bin:$PATH"
```

**Windows x86_64 (PowerShell):**
```powershell
Invoke-WebRequest -Uri https://github.com/simple-lang/simple/releases/download/v0.5.0/simple-0.5.0-windows-x86_64.zip -OutFile simple.zip
Expand-Archive simple.zip
cd simple-0.5.0
$env:PATH = "$PWD\bin;$env:PATH"
```

### Verify Installation

```bash
simple --version
# Output: Simple 0.5.0 (2026-02-06)
```

### Add to PATH Permanently

**Linux/macOS (bash/zsh):**
```bash
# Add to ~/.bashrc or ~/.zshrc
export PATH="/path/to/simple-0.5.0/bin:$PATH"

# Reload shell
source ~/.bashrc  # or ~/.zshrc
```

**Windows (PowerShell):**
```powershell
# Add to PowerShell profile
$profile_path = "$HOME\Documents\PowerShell\Microsoft.PowerShell_profile.ps1"
Add-Content $profile_path '$env:PATH = "C:\path\to\simple-0.5.0\bin;$env:PATH"'

# Reload profile
. $profile_path
```

---

## Your First Program

### Hello World

Create a file named `hello.spl`:

```simple
fn main():
    print "Hello, World!"
```

Run it:
```bash
simple hello.spl
# Output: Hello, World!
```

**Explanation:**
- `fn main()` - Entry point function
- `print` - Built-in print function
- Strings use double quotes with automatic interpolation

### Exit Codes

```simple
fn main() -> i64:
    print "Exiting with code 42"
    return 42
```

Run and check exit code:
```bash
simple exit_code.spl
echo $?  # Linux/macOS
echo $LASTEXITCODE  # Windows PowerShell
# Output: 42
```

### Variables

```simple
fn main():
    # Immutable variables (preferred)
    val name = "Alice"
    val age = 30

    # Mutable variables
    var count = 0
    count = count + 1

    # String interpolation
    print "Hello, {name}! You are {age} years old."
    print "Count: {count}"
```

**Output:**
```
Hello, Alice! You are 30 years old.
Count: 1
```

---

## Basic Types and Operations

### Numbers

```simple
fn main():
    # Integers
    val x: i32 = 42
    val y: i64 = 1000000

    # Floats
    val pi: f64 = 3.14159
    val ratio: f32 = 0.5

    # Arithmetic
    print "Sum: {x + 10}"
    print "Product: {x * 2}"
    print "Division: {x / 2}"
    print "Modulo: {x % 5}"
```

### Strings

```simple
fn main():
    val greeting = "Hello"
    val name = "World"

    # Concatenation with interpolation
    val message = "{greeting}, {name}!"
    print message  # Hello, World!

    # String methods
    print greeting.upper()  # HELLO
    print greeting.lower()  # hello
    print name.len()        # 5

    # Slicing
    print greeting[0:2]     # He
    print greeting[1:]      # ello
    print greeting[:4]      # Hell
```

### Booleans

```simple
fn main():
    val is_valid = true
    val is_error = false

    # Logical operations
    print is_valid and not is_error  # true
    print is_valid or is_error       # true
    print not is_error               # true
```

---

## Control Flow

### If/Else

```simple
fn check_age(age: i64):
    if age >= 18:
        print "Adult"
    elif age >= 13:
        print "Teenager"
    else:
        print "Child"

fn main():
    check_age(25)  # Adult
    check_age(15)  # Teenager
    check_age(10)  # Child
```

### Loops

**For loop:**
```simple
fn main():
    # Range (exclusive)
    for i in 0..5:
        print i  # 0, 1, 2, 3, 4

    # Range (inclusive)
    for i in 0..=5:
        print i  # 0, 1, 2, 3, 4, 5

    # Array iteration
    val items = [10, 20, 30]
    for item in items:
        print item
```

**While loop:**
```simple
fn main():
    var count = 0
    while count < 5:
        print count
        count = count + 1
```

**Infinite loop:**
```simple
fn main():
    var count = 0
    loop:
        print count
        count = count + 1
        if count >= 5:
            break
```

---

## Collections

### Arrays

```simple
fn main():
    # Array literal
    val numbers = [1, 2, 3, 4, 5]

    # Indexing
    print numbers[0]      # 1
    print numbers[-1]     # 5 (last element)

    # Slicing
    print numbers[1:3]    # [2, 3]

    # Methods
    print numbers.len()   # 5
    print numbers.first() # 1
    print numbers.last()  # 5

    # Array operations
    val doubled = numbers.map(\x: x * 2)
    val evens = numbers.filter(\x: x % 2 == 0)
    val sum = numbers.fold(0, \acc, x: acc + x)
```

### Dictionaries

```simple
fn main():
    # Dictionary literal
    val scores = {"alice": 100, "bob": 85, "carol": 92}

    # Access
    print scores["alice"]  # 100

    # Optional access
    val dave_score = scores["dave"]
    print dave_score  # nil (missing key)

    # Default value
    print scores.get("dave", 0)  # 0

    # Iteration
    for (name, score) in scores.items():
        print "{name}: {score}"
```

---

## Functions

### Basic Functions

```simple
fn add(a: i64, b: i64) -> i64:
    return a + b

fn greet(name: text):
    print "Hello, {name}!"

fn main():
    val result = add(5, 3)
    print result  # 8

    greet("Alice")  # Hello, Alice!
```

### Implicit Return

```simple
fn square(x: i64) -> i64:
    x * x  # Last expression is returned

fn main():
    print square(5)  # 25
```

### Multiple Return Values

```simple
fn divide(a: i64, b: i64) -> (i64, i64):
    val quotient = a / b
    val remainder = a % b
    return (quotient, remainder)

fn main():
    val (quot, rem) = divide(17, 5)
    print "Quotient: {quot}, Remainder: {rem}"
    # Output: Quotient: 3, Remainder: 2
```

### Lambda Functions

```simple
fn main():
    val double = \x: x * 2
    print double(5)  # 10

    val add = \a, b: a + b
    print add(3, 4)  # 7

    # Higher-order functions
    val numbers = [1, 2, 3, 4, 5]
    val doubled = numbers.map(\x: x * 2)
    print doubled  # [2, 4, 6, 8, 10]
```

---

## Structs and Classes

### Structs (Value Types)

```simple
struct Point:
    x: f64
    y: f64

fn main():
    val p = Point(x: 3.0, y: 4.0)
    print "Point: ({p.x}, {p.y})"

    val distance = (p.x * p.x + p.y * p.y).sqrt()
    print "Distance from origin: {distance}"
```

### Classes (Reference Types)

```simple
class Person:
    name: text
    age: i64

    fn greet():
        print "Hello, I'm {self.name}"

    fn birthday():
        self.age = self.age + 1
        print "{self.name} is now {self.age}"

fn main():
    val alice = Person(name: "Alice", age: 30)
    alice.greet()      # Hello, I'm Alice
    alice.birthday()   # Alice is now 31
```

---

## Pattern Matching

### Enums

```simple
enum Result<T, E>:
    Ok(value: T)
    Err(error: E)

fn divide(a: i64, b: i64) -> Result<i64, text>:
    if b == 0:
        return Result.Err("Division by zero")
    return Result.Ok(a / b)

fn main():
    val result = divide(10, 2)

    match result:
        case Ok(value):
            print "Result: {value}"
        case Err(error):
            print "Error: {error}"
```

### Option Type

```simple
fn find_user(id: i64) -> Option<text>:
    if id == 1:
        return Some("Alice")
    return None

fn main():
    val user = find_user(1)

    match user:
        case Some(name):
            print "Found: {name}"
        case None:
            print "User not found"

    # Optional chaining
    val name = user?.upper() ?? "UNKNOWN"
    print name  # ALICE
```

---

## Error Handling

### Result Type

```simple
fn read_config(path: text) -> Result<text, text>:
    if not file_exists(path):
        return Err("File not found: {path}")

    val content = read_file(path)
    if content.is_empty():
        return Err("File is empty")

    return Ok(content)

fn main():
    match read_config("config.txt"):
        case Ok(content):
            print "Config loaded: {content}"
        case Err(error):
            print "Error: {error}"
```

### Try Operator (`?`)

```simple
fn load_and_parse(path: text) -> Result<i64, text>:
    val content = read_config(path)?  # Propagates error
    val value = parse_int(content)?   # Propagates error
    return Ok(value)

fn main():
    match load_and_parse("data.txt"):
        case Ok(value):
            print "Parsed: {value}"
        case Err(error):
            print "Failed: {error}"
```

---

## Modules and Imports

### Importing Standard Library

```simple
# Import specific functions
import std.math (sqrt, pow, abs)

fn main():
    print sqrt(16.0)   # 4.0
    print pow(2.0, 3)  # 8.0
    print abs(-10)     # 10
```

### Importing Modules

```simple
# Import entire module
import std.collections

fn main():
    val list = collections.List.new()
    list.append(1)
    list.append(2)
    print list  # [1, 2]
```

### Creating Modules

**File: math_utils.spl**
```simple
export fn double(x: i64) -> i64:
    x * 2

export fn triple(x: i64) -> i64:
    x * 3
```

**File: main.spl**
```simple
import math_utils

fn main():
    print math_utils.double(5)  # 10
    print math_utils.triple(5)  # 15
```

---

## File I/O

### Reading Files

```simple
import std.io (read_file, write_file)

fn main():
    # Read entire file
    val content = read_file("data.txt")
    print content

    # Read lines
    val lines = read_file("data.txt").split("\n")
    for line in lines:
        print line
```

### Writing Files

```simple
import std.io (write_file)

fn main():
    val data = "Hello, World!\nThis is a test."
    write_file("output.txt", data)
    print "File written successfully"
```

---

## Command-Line Arguments

```simple
import std.env (args)

fn main():
    val arguments = args()

    if arguments.len() < 2:
        print "Usage: simple program.spl <name>"
        return

    val name = arguments[1]
    print "Hello, {name}!"
```

Run:
```bash
simple greet.spl Alice
# Output: Hello, Alice!
```

---

## Testing with SSpec

### Writing Tests

**File: math_spec.spl**
```simple
import std.spec

describe "Math operations":
    it "adds two numbers":
        val result = 2 + 3
        expect(result).to_equal(5)

    it "multiplies two numbers":
        val result = 4 * 5
        expect(result).to_equal(20)

    it "handles negative numbers":
        val result = -5 + 10
        expect(result).to_equal(5)
```

### Running Tests

```bash
simple test math_spec.spl
```

**Output:**
```
Math operations
  ✓ adds two numbers
  ✓ multiplies two numbers
  ✓ handles negative numbers

3 passed, 0 failed
```

---

## Building Projects

### Simple Build System

**File: simple.sdn**
```sdn
package:
  name: myproject
  version: 0.1.0

dependencies:
  http: 2.0
  json: 1.5
```

### Build Commands

```bash
# Build project
simple build

# Run tests
simple test

# Build optimized release
simple build --release

# Clean build artifacts
simple build clean
```

---

## Next Steps

**Learn more:**
- [Language Specification](../spec/README.md)
- [Architecture Guide](architecture.md)
- [Standard Library Reference](../spec/stdlib.md)
- [Advanced Features](../spec/README.md#advanced-features)

**Try examples:**
```bash
# Explore examples
cd simple-0.5.0/examples/

# Run examples
simple examples/hello.spl
simple examples/fibonacci.spl
simple examples/web_server.spl
```

**Get help:**
- [GitHub Issues](https://github.com/simple-lang/simple/issues)
- [Documentation](https://simple-lang.org/docs)
- [Community Forum](https://forum.simple-lang.org)

---

## Common Tasks

### Compile to Binary

```bash
# Compile to executable
simple compile myprogram.spl -o myprogram

# Run the binary
./myprogram
```

### Watch Mode (Auto-Rebuild)

```bash
# Watch file for changes
simple watch myprogram.spl

# Auto-rebuild on save
simple build watch
```

### Check Code Quality

```bash
# Format code
simple build fmt

# Run linter
simple build lint

# Run all checks
simple build check
```

---

## Summary

You now know:
- ✅ How to install Simple
- ✅ Basic syntax (variables, types, control flow)
- ✅ Collections (arrays, dictionaries)
- ✅ Functions and lambdas
- ✅ Structs and classes
- ✅ Pattern matching
- ✅ Error handling
- ✅ File I/O
- ✅ Testing with SSpec
- ✅ Building projects

**Ready to build something?** Check out the [examples/](../../examples/) directory for real-world code samples!
