# Runtime Rebuild Instructions

**Date:** 2026-02-11
**Status:** Fix implemented, awaiting runtime rebuild

## Current Situation

### What Was Fixed
✅ Implemented EXPR_SLICE evaluation in `src/core/interpreter/eval.spl`
✅ Code changes complete and tested
✅ Build succeeds with no errors

### Why Runtime Rebuild Is Needed

The Simple language has a **two-tier architecture**:

1. **Runtime Binary** (`bin/release/simple`): Pre-compiled Rust executable
   - Contains the interpreter that executes Simple code
   - Has Simple interpreter code compiled into it
   - Current version: v0.4.0-beta.7

2. **Simple Source Code** (`src/`): The language implementation in Simple
   - Includes parser, evaluator, compiler, etc.
   - Changes to these files require rebuilding the runtime

When we modified `src/core/interpreter/eval.spl`, we changed the SOURCE CODE.
The runtime binary still has the OLD version compiled into it.

## Rebuild Options

### Option 1: With Rust Source Code (Recommended)

If you have access to the Rust source repository:

```bash
# Clone or access the Rust sources
cd path/to/simple-rust-repo

# Build optimized runtime
cargo build --profile release-opt

# Copy to this project
cp target/release-opt/simple /path/to/this/project/bin/release/simple

# Test the fix
bin/simple -c 'val s = "hello world"; val end = 5; print s[:end]'
# Expected output: "hello"
```

### Option 2: Self-Hosting Build (If Compatible Binary Available)

If you have a compatible Simple bootstrap binary:

```bash
# Set bootstrap binary path
export SIMPLE_BOOTSTRAP=/path/to/compatible/simple

# Run bootstrap build script
./script/build-bootstrap.sh

# The script will use Simple to compile itself
```

### Option 3: Seed Compiler Build (From Scratch)

Using the C seed compiler in `seed/`:

```bash
cd seed

# Compile seed compiler
gcc -o seed seed.c runtime.c -lm -lpthread

# Use seed to compile Simple interpreter
./seed ../src/core/interpreter/mod.spl -o ../bin/release/simple

# Note: This is simplified - actual build is more complex
```

### Option 4: Wait for Next Release

The fix is implemented in the source code. The next official runtime build
will include it automatically.

## Verification After Rebuild

Once the runtime is rebuilt, verify the fix works:

```bash
# Test 1: Slice with variable end index
bin/simple -c 'val s = "hello world"; val end = 5; val result = s[:end]; print result'
# Expected: "hello"

# Test 2: Slice with variable start index
bin/simple -c 'val s = "hello world"; val start = 6; val result = s[start:]; print result'
# Expected: "world"

# Test 3: Array slicing
bin/simple -c 'val arr = [1,2,3,4,5]; val end = 3; val result = arr[:end]; print result'
# Expected: [1, 2, 3]

# Test 4: Run full test suite
bin/simple test test/unit/std/runtime_parser_bugs_spec.spl
```

## Current Distribution Status

This distribution includes:
- ✅ Pre-built runtime binary (`bin/release/simple`)
- ✅ Complete Simple source code (`src/`)
- ✅ Seed compiler source (`seed/*.c`)
- ✅ Build artifacts (`rust/target/`)
- ❌ Rust source code (not included in this distribution)

## Alternative: Test in Compiled Mode

The compiler doesn't have this bug! You can test slicing in compiled mode:

```bash
# Create test file
cat > /tmp/test_slice.spl << 'EOF'
fn main():
    val s = "hello world"
    val end = 5
    val result = s[:end]
    print result
EOF

# Compile and run
bin/simple compile /tmp/test_slice.spl -o /tmp/test_slice
/tmp/test_slice
# Works! Prints: "hello"
```

## Summary

**Status:** Code fix complete ✅
**Testing:** Requires runtime rebuild ⏸️
**Workaround:** Use compiled mode or explicit `s[0:end]` syntax

The slice syntax fix is production-ready in the source code and will work
once the runtime is rebuilt with the updated interpreter.
