# Getting Started with Simple

This guide covers installation, your first program, and the core language features you need to start writing Simple code.

---

## Installation

### Quick Install (Linux / macOS)

```bash
curl -fsSL https://install.simple-lang.org/bootstrap.sh | sh
```

Or with a custom directory:

```bash
SIMPLE_INSTALL_DIR=/opt/simple curl -fsSL https://install.simple-lang.org/bootstrap.sh | sh
```

### Package Managers

**macOS (Homebrew):**
```bash
brew install simple-lang/tap/simple
```

**Ubuntu/Debian:**
```bash
sudo apt-get install simple-lang
```

**Fedora/RHEL:**
```bash
sudo dnf install simple-lang
```

**Arch Linux:**
```bash
yay -S simple-lang
```

**Windows (Chocolatey):**
```powershell
choco install simple-lang
```

### Manual Download

Download pre-compiled releases from [GitHub Releases](https://github.com/simple-lang/simple/releases).

**Linux x86_64:**
```bash
wget https://github.com/simple-lang/simple/releases/download/v0.5.0/simple-0.5.0-linux-x86_64.tar.gz
tar -xzf simple-0.5.0-linux-x86_64.tar.gz
export PATH="$PWD/simple-0.5.0/bin:$PATH"
```

**macOS ARM64 (Apple Silicon):**
```bash
curl -LO https://github.com/simple-lang/simple/releases/download/v0.5.0/simple-0.5.0-darwin-aarch64.tar.gz
tar -xzf simple-0.5.0-darwin-aarch64.tar.gz
export PATH="$PWD/simple-0.5.0/bin:$PATH"
```

**Windows (PowerShell):**
```powershell
Invoke-WebRequest -Uri https://github.com/simple-lang/simple/releases/download/v0.5.0/simple-0.5.0-windows-x86_64.zip -OutFile simple.zip
Expand-Archive simple.zip
$env:PATH = "$PWD\simple-0.5.0\bin;$env:PATH"
```

### Add to PATH Permanently

**bash/zsh:**
```bash
echo 'export PATH="$HOME/.local/bin:$PATH"' >> ~/.bashrc   # or ~/.zshrc
source ~/.bashrc
```

**PowerShell:**
```powershell
$path = [Environment]::GetEnvironmentVariable("Path", "User")
[Environment]::SetEnvironmentVariable("Path", "$path;$env:LOCALAPPDATA\Simple\bin", "User")
```

### Verify Installation

```bash
simple --version
```

### System Requirements

- **OS**: Linux (kernel 4.4+), macOS 10.13+, Windows 10+
- **CPU**: x86_64 or ARM64
- **RAM**: 256 MB minimum, 1 GB recommended
- **Disk**: 50 MB minimum

---

## Your First Program

### Hello World

Create `hello.spl`:

```simple
fn main():
    print "Hello, World!"
```

Run it:

```bash
simple hello.spl
# Output: Hello, World!
```

- `fn main()` is the entry point function.
- `print` is the built-in print function.
- Strings use double quotes with automatic interpolation.

### Variables and Interpolation

```simple
fn main():
    val name = "Alice"          # Immutable (preferred)
    var count = 0               # Mutable
    count = count + 1

    print "Hello, {name}!"     # String interpolation
    print "Count: {count}"
```

### Exit Codes

```simple
fn main() -> i64:
    print "Done"
    return 42
```

```bash
simple exit_code.spl; echo $?
# 42
```

---

## Basic Types

```simple
fn main():
    val x: i64 = 42            # Integer
    val pi: f64 = 3.14159      # Float
    val ok: bool = true         # Boolean
    val msg: text = "hello"     # String

    # Arithmetic
    print "Sum: {x + 10}"
    print "Power: {x ** 2}"

    # String methods
    print msg.upper()           # HELLO
    print msg.len()             # 5

    # Logical operators
    print ok and not false      # true
```

---

## Control Flow

```simple
fn check_age(age: i64):
    if age >= 18:
        print "Adult"
    elif age >= 13:
        print "Teenager"
    else:
        print "Child"

fn main():
    # For loop (exclusive range)
    for i in 0..5:
        print i                 # 0, 1, 2, 3, 4

    # For loop (inclusive range)
    for i in 0..=3:
        print i                 # 0, 1, 2, 3

    # While loop
    var count = 0
    while count < 5:
        count = count + 1

    # Infinite loop with break
    loop:
        if count >= 10:
            break
        count = count + 1
```

---

## Collections

### Arrays

```simple
fn main():
    val numbers = [1, 2, 3, 4, 5]
    print numbers[0]            # 1
    print numbers[-1]           # 5 (last)
    print numbers[1:3]          # [2, 3]
    print numbers.len()         # 5

    val doubled = numbers.map(\x: x * 2)
    val evens = numbers.filter(\x: x % 2 == 0)
    val sum = numbers.fold(0, \acc, x: acc + x)
```

### Dictionaries

```simple
fn main():
    val scores = {"alice": 100, "bob": 85}
    print scores["alice"]       # 100
    print scores.get("dave", 0) # 0 (default)

    for (name, score) in scores.items():
        print "{name}: {score}"
```

---

## Functions

```simple
fn square(x: i64) -> i64:
    x * x                       # Implicit return

fn divide(a: i64, b: i64) -> (i64, i64):
    return (a / b, a % b)       # Multiple return values

fn main():
    print square(5)             # 25

    val (q, r) = divide(17, 5)
    print "Quotient: {q}, Remainder: {r}"

    # Lambdas
    val double = \x: x * 2
    print double(5)             # 10

    val nums = [1, 2, 3]
    print nums.map(_ * 2)       # [2, 4, 6]  (placeholder lambda)
    print nums.map(&:to_text)   # Method reference
```

---

## Structs and Classes

```simple
struct Point:
    x: f64
    y: f64

class Person:
    name: text
    age: i64

    fn greet():
        print "Hello, I'm {self.name}"

    me birthday():              # Mutable method ('me')
        self.age = self.age + 1

fn main():
    val p = Point(x: 3.0, y: 4.0)
    print "({p.x}, {p.y})"

    val alice = Person(name: "Alice", age: 30)
    alice.greet()
    alice.birthday()
```

---

## Pattern Matching and Error Handling

```simple
fn find_user(id: i64) -> Option<text>:
    if id == 1:
        return Some("Alice")
    return None

fn read_config(path: text) -> Result<text, text>:
    if not file_exists(path):
        return Err("File not found: {path}")
    return Ok(read_file(path))

fn main():
    # Pattern matching
    match find_user(1):
        case Some(name):
            print "Found: {name}"
        case None:
            print "Not found"

    # Optional chaining + coalescing
    val name = find_user(1)?.upper() ?? "UNKNOWN"

    # Try operator (propagates errors)
    match read_config("config.txt"):
        case Ok(content): print content
        case Err(e): print "Error: {e}"
```

---

## Modules and Imports

```simple
# Import from standard library
import std.math (sqrt, pow, abs)

# Import entire module
import std.collections

fn main():
    print sqrt(16.0)            # 4.0
```

Create your own modules:

```simple
# math_utils.spl
export fn double(x: i64) -> i64:
    x * 2
```

```simple
# main.spl
import math_utils
fn main():
    print math_utils.double(5)  # 10
```

---

## Testing with SSpec

Create `math_spec.spl`:

```simple
import std.spec

describe "Math operations":
    it "adds two numbers":
        expect(2 + 3).to_equal(5)

    it "multiplies two numbers":
        expect(4 * 5).to_equal(20)
```

Run tests:

```bash
simple test math_spec.spl
```

---

## Building Projects

### Project Configuration (`simple.sdn`)

```sdn
package:
  name: myproject
  version: 0.1.0

dependencies:
  http: 2.0
  json: 1.5
```

### Commands

```bash
simple build                    # Build project
simple build --release          # Optimized build
simple test                     # Run all tests
simple build fmt                # Format code
simple build lint               # Run linter
simple build check              # All quality checks
```

### Compile to Binary

```bash
simple compile myprogram.spl -o myprogram
./myprogram
```

---

## Troubleshooting

**`simple: command not found`** -- Verify the `bin` directory is in your PATH and reload your shell config.

**Permission denied (Linux/macOS):** `chmod +x ~/.local/bin/simple`

**macOS security warning:** `xattr -d com.apple.quarantine ~/.local/lib/simple/simple_runtime`

**Library not found (Linux):** `sudo ldconfig` or set `LD_LIBRARY_PATH`.

---

## Next Steps

- [CLI Reference](cli.md) -- command-line options and subcommands
- [Build Guide](build.md) -- build system, bootstrap, and SDN configuration
- [Syntax Quick Reference](quick_reference/syntax_quick_reference.md) -- full language syntax
- [Standard Library Reference](../spec/stdlib.md)
