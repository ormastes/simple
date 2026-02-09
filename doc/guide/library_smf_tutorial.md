# Library SMF Tutorial: Build Your First Library

**Duration:** 30 minutes
**Level:** Beginner to Intermediate
**Prerequisites:** Basic Simple programming knowledge

## What You'll Build

By the end of this tutorial, you'll have:
- ✅ A working math library (libmath.lsm)
- ✅ A program that uses your library
- ✅ Experience with library creation and management
- ✅ Knowledge of native linking with libraries

---

## Part 1: Setup (5 minutes)

### Step 1: Create Project Structure

```bash
mkdir -p simple-library-tutorial
cd simple-library-tutorial

# Create directories
mkdir -p {src/math,build/{smf,obj},app}
```

**Result:**
```
simple-library-tutorial/
├── src/math/      # Library source code
├── build/smf/     # Compiled SMF files
├── build/obj/     # Compiled object files
└── app/           # Application code
```

### Step 2: Verify Simple Installation

```bash
simple --version
# Should output: Simple v0.5.0 or later
```

If not installed, see [Installation Guide](../install.md).

---

## Part 2: Write Library Code (10 minutes)

### Step 3: Create Math Functions

**File: `src/math/arithmetic.spl`**
```simple
# Basic arithmetic operations

fn add(a: i64, b: i64) -> i64:
    """Add two integers."""
    a + b

fn subtract(a: i64, b: i64) -> i64:
    """Subtract b from a."""
    a - b

fn multiply(a: i64, b: i64) -> i64:
    """Multiply two integers."""
    a * b

fn divide(a: i64, b: i64) -> Result<i64, text>:
    """Divide a by b, returning error if b is zero."""
    if b == 0:
        return Err("Division by zero")
    Ok(a / b)

# Export functions
export add, subtract, multiply, divide
```

**File: `src/math/stats.spl`**
```simple
# Statistical functions

fn sum(numbers: [i64]) -> i64:
    """Calculate sum of array."""
    var total: i64 = 0
    for n in numbers:
        total = total + n
    total

fn mean(numbers: [i64]) -> Result<f64, text>:
    """Calculate arithmetic mean."""
    if numbers.len() == 0:
        return Err("Cannot calculate mean of empty array")

    val total = sum(numbers)
    val count = numbers.len()
    Ok(total as f64 / count as f64)

fn min(numbers: [i64]) -> Result<i64, text>:
    """Find minimum value."""
    if numbers.len() == 0:
        return Err("Cannot find min of empty array")

    var minimum = numbers[0]
    for n in numbers:
        if n < minimum:
            minimum = n
    Ok(minimum)

fn max(numbers: [i64]) -> Result<i64, text>:
    """Find maximum value."""
    if numbers.len() == 0:
        return Err("Cannot find max of empty array")

    var maximum = numbers[0]
    for n in numbers:
        if n > maximum:
            maximum = n
    Ok(maximum)

# Export functions
export sum, mean, min, max
```

### Step 4: Verify Code Compiles

```bash
# Check syntax
simple check src/math/arithmetic.spl
simple check src/math/stats.spl

# Expected output:
# ✓ No errors found
```

---

## Part 3: Compile Library (10 minutes)

### Step 5: Compile to SMF and Objects

**Option A: Manual Compilation**
```bash
# Arithmetic module
simple compile src/math/arithmetic.spl --emit-smf -o build/smf/math_arithmetic.smf
simple compile src/math/arithmetic.spl --emit-obj -o build/obj/math_arithmetic.o

# Stats module
simple compile src/math/stats.spl --emit-smf -o build/smf/math_stats.smf
simple compile src/math/stats.spl --emit-obj -o build/obj/math_stats.o
```

**Option B: Automated Script (Recommended)**
```bash
# Compile all modules at once
simple script/compile_with_objects.spl \
    --input-dir=src/math \
    --output-dir=build \
    --verbose
```

**Output:**
```
========================================
Compiling Modules with Object Files
========================================

Input:  src/math
Output: build

[1/4] Creating output directories...
[2/4] Finding source files...
Found 2 source files
[3/4] Compiling files...
  src/math/arithmetic.spl
    → SMF: build/smf/math/arithmetic.smf
    → OBJ: build/obj/math/arithmetic.o
    ✓ Success
  src/math/stats.spl
    → SMF: build/smf/math/stats.smf
    → OBJ: build/obj/math/stats.o
    ✓ Success

Compilation complete:
  Success: 2
  Errors:  0
```

### Step 6: Create Library Archive

```bash
# Create libmath.lsm from compiled modules
simple script/lib_tool.spl create libmath.lsm \
    build/smf/math/arithmetic.smf \
    build/smf/math/stats.smf
```

**Output:**
```
Creating library: libmath.lsm
Input files: 2

  Adding: math_arithmetic (build/smf/math/arithmetic.smf)
  Adding: math_stats (build/smf/math/stats.smf)

Writing library...
✓ Library created successfully
  Output: libmath.lsm
```

### Step 7: Verify Library

```bash
# List modules
simple script/lib_tool.spl list libmath.lsm
```

**Output:**
```
Listing modules in: libmath.lsm

Modules (2):
  - math_arithmetic
  - math_stats
```

```bash
# Verify integrity
simple script/lib_tool.spl verify libmath.lsm
```

**Output:**
```
Verifying library: libmath.lsm

Checking 2 modules...
  ✓ math_arithmetic
  ✓ math_stats

Results:
  Verified: 2
  Failed: 0

✓ All modules verified
```

---

## Part 4: Use Your Library (10 minutes)

### Step 8: Write Application Code

**File: `app/calculator.spl`**
```simple
use math_arithmetic.{add, subtract, multiply, divide}
use math_stats.{sum, mean, min, max}

fn main():
    print("========================================")
    print("Calculator Demo - Using libmath.lsm")
    print("========================================")
    print("")

    # Test arithmetic
    print("Arithmetic Operations:")
    print("  10 + 5 = {add(10, 5)}")
    print("  10 - 5 = {subtract(10, 5)}")
    print("  10 * 5 = {multiply(10, 5)}")

    val div_result = divide(10, 5)
    match div_result:
        case Ok(value):
            print("  10 / 5 = {value}")
        case Err(e):
            print("  10 / 5 = Error: {e}")

    print("")

    # Test statistics
    print("Statistical Functions:")
    val numbers = [5, 2, 8, 1, 9, 3]
    print("  Numbers: [5, 2, 8, 1, 9, 3]")
    print("  Sum: {sum(numbers)}")

    val mean_result = mean(numbers)
    if mean_result.is_ok():
        print("  Mean: {mean_result.unwrap()}")

    val min_result = min(numbers)
    if min_result.is_ok():
        print("  Min: {min_result.unwrap()}")

    val max_result = max(numbers)
    if max_result.is_ok():
        print("  Max: {max_result.unwrap()}")

    print("")
    print("========================================")
```

### Step 9: Compile Application

```bash
# Compile to object file
simple compile app/calculator.spl --emit-obj -o app/calculator.o
```

### Step 10: Link with Library

**Option A: Command Line**
```bash
simple link app/calculator.o \
    --libraries=./libmath.lsm \
    --output=calculator
```

**Option B: Programmatic (create link script)**

**File: `app/link.spl`**
```simple
use compiler.linker.linker_wrapper_lib_support.{link_with_libraries}
use compiler.linker.linker_wrapper.{NativeLinkConfig}

fn main():
    var config = NativeLinkConfig.default()
    config.library_paths = ["."]
    config.verbose = true

    val objects = ["app/calculator.o"]

    print("Linking calculator with libmath.lsm...")

    val result = link_with_libraries(objects, "calculator", config)

    match result:
        case Ok(path):
            print("✓ Success: {path}")
        case Err(e):
            print("✗ Error: {e}")
            exit(1)
```

```bash
# Run link script
simple run app/link.spl
```

### Step 11: Run Your Program

```bash
./calculator
```

**Expected Output:**
```
========================================
Calculator Demo - Using libmath.lsm
========================================

Arithmetic Operations:
  10 + 5 = 15
  10 - 5 = 5
  10 * 5 = 50
  10 / 5 = 2

Statistical Functions:
  Numbers: [5, 2, 8, 1, 9, 3]
  Sum: 28
  Mean: 4.666667
  Min: 1
  Max: 9

========================================
```

🎉 **Congratulations!** You've successfully created and used a library!

---

## Part 5: Advanced Features (Bonus)

### Extract and Inspect Modules

```bash
# Extract arithmetic module
simple script/lib_tool.spl extract libmath.lsm math_arithmetic --output=arithmetic.smf

# Inspect with hexdump (first 128 bytes = SMF header)
hexdump -C arithmetic.smf | head -n 8
```

### Update Library

```bash
# Add a new module
echo 'fn square(x: i64) -> i64: x * x' > src/math/power.spl
echo 'export square' >> src/math/power.spl

# Compile it
simple compile src/math/power.spl --emit-smf -o build/smf/math/power.smf

# Rebuild library with new module
simple script/lib_tool.spl create libmath.lsm \
    build/smf/math/arithmetic.smf \
    build/smf/math/stats.smf \
    build/smf/math/power.smf

# Verify
simple script/lib_tool.spl list libmath.lsm
# Now shows 3 modules!
```

### View Library Details

```bash
simple script/lib_tool.spl info libmath.lsm
```

**Output:**
```
Library Information
===================
Path: libmath.lsm
Size: 16384 bytes
Format: Library SMF v1.0
Modules: 3

Module List:
  math_arithmetic
    Offset: 256
    Size: 4096 bytes
    Hash: 0x1234567890abcdef
  math_stats
    Offset: 4352
    Size: 5120 bytes
    Hash: 0x234567890abcdef1
  math_power
    Offset: 9472
    Size: 2048 bytes
    Hash: 0x34567890abcdef12
```

---

## Common Issues and Solutions

### Issue 1: Module Not Found

**Error:**
```
Error: Module not found: 'math_arithmetic'
```

**Solution:**
```bash
# Check module name in library
simple script/lib_tool.spl list libmath.lsm

# Use exact name from library
use math_arithmetic.{add}  # Correct
use math.arithmetic.{add}  # Wrong
```

### Issue 2: Object File Not Found

**Error:**
```
Error: Object file not found for module 'math_arithmetic'
```

**Solution:**
```bash
# Compile with object files
simple compile src/math/arithmetic.spl --emit-obj -o build/obj/math_arithmetic.o

# Or use helper script
simple script/compile_with_objects.spl --input-dir=src/math
```

### Issue 3: Symbol Not Found

**Error:**
```
Error: Undefined symbol 'add'
```

**Solution:**
```simple
# Make sure function is exported
fn add(a: i64, b: i64) -> i64: a + b
export add  # ← Add this line
```

---

## Next Steps

### Learn More
- Read the [User Guide](library_smf_user_guide.md) for complete API reference
- See the [Format Specification](../format/lib_smf_specification.md) for technical details
- Browse [Example Projects](../../examples/lib_smf/) for more complex use cases

### Build Something
- Create a string utilities library
- Package your application's common code as a library
- Contribute to the standard library

### Share Your Work
- Publish your library on GitHub
- Share on Simple Discord community
- Write a blog post about your experience

---

## Summary

In this tutorial, you:
- ✅ Created a math library with arithmetic and statistics functions
- ✅ Compiled modules to both SMF and object files
- ✅ Built a library archive (libmath.lsm)
- ✅ Wrote an application that uses your library
- ✅ Linked and ran a program using library modules
- ✅ Learned library management commands

**Key Takeaways:**
- Libraries bundle multiple modules into one file
- Both SMF and object files are needed for linking
- The lib_tool script provides easy library management
- Library linking is transparent and fast

**Happy coding with Simple libraries!** 🚀

---

**Questions?** Ask on [Discord](https://discord.gg/simple-lang) or open an issue on [GitHub](https://github.com/simple-lang/simple/issues)
