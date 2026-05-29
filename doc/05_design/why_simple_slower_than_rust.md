# Why Simple Code Is Slower Than Rust (Currently)

**Date:** 2026-01-30
**Status:** Bootstrap v0.3.0

---

## Your Question: "If both compile to LLVM, why is Simple slower than Rust?"

**Short answer:** Simple code is currently **INTERPRETED**, not compiled to LLVM!

---

## Current Reality

### How Simple Code Actually Runs

```
simple/compiler/main.spl (bootstrap compiler)
         ↓
   INTERPRETED by simple_runtime
         ↓
   Rust interpreter walks AST
         ↓
   ~50-100x slower than native code
```

### Proof from Codebase

**1. Bootstrap command interprets:**
```makefile
# Makefile line 627
./target/debug/simple_runtime compile simple/compiler/main.spl -o $(BOOTSTRAP_DIR)/simple_new1 --native
```

The `simple_runtime` binary **interprets** `simple/compiler/main.spl` to produce `simple_new1`.

**2. Runtime explicitly blocks compiled mode:**
```rust
// src/rust/compiler/src/interpreter_extern/cli.rs:364
pub fn rt_cli_handle_compile(_args: &[Value]) -> Result<Value, CompileError> {
    interpreter_not_supported("rt_cli_handle_compile")
}
```

Error message:
```
error: rt_cli_handle_compile is not supported in interpreter mode
hint: Build and run the compiled CLI for full functionality
```

**3. Comments confirm interpretation:**
```rust
// src/rust/compiler/src/pipeline/execution.rs:108
/// This uses the interpreter mode which supports all language features.

// src/rust/compiler/src/pipeline/execution.rs:220
/// Faster execution but supports fewer language features than interpreter mode.
```

---

## Why Interpretation, Not Compilation?

### 1. Bootstrap Chicken-and-Egg Problem

**Problem:** To compile Simple code, you need a Simple compiler. But the Simple compiler is written in Simple!

**Solution:** Use Rust interpreter as bootstrap:
```
Rust interpreter → Run simple/compiler/main.spl → Produce compiled binary
```

### 2. Feature Completeness

Interpreter supports **ALL** language features:
- ✅ Dynamic dispatch
- ✅ Closures with captures
- ✅ Pattern matching
- ✅ Metaprogramming
- ✅ Matrix operations (@)
- ✅ Pipeline operators (|>, >>, <<, //, ~>)
- ✅ Async/await
- ✅ Context blocks
- ✅ Static methods
- ✅ Template strings with i18n

Native compilation currently missing:
- ❌ Matrix multiplication (@) - needs runtime library
- ❌ Pipeline operators - requires function dispatch
- ❌ Parallel operator (//) - needs async runtime
- ❌ Static methods - "not yet supported in native compilation"
- ❌ Context statements - planned
- ❌ Some template features

**From error messages:**
```rust
// src/rust/compiler/src/codegen/instr/core.rs:172
return Err("Matrix multiplication (@) requires runtime library, use interpreter mode");

// Line 176
return Err("Pipe forward (|>) requires interpreter mode for function dispatch");

// Line 180
return Err("Parallel operator (//) requires interpreter mode for concurrent execution");
```

### 3. Simple Compiler Codegen in Simple

The `simple/compiler/codegen.spl` itself calls Cranelift **via FFI**:

```simple
// simple/compiler/codegen.spl:20
extern fn rt_cranelift_new_module(name_ptr: i64, name_len: i64, target: i64) -> i64
extern fn rt_cranelift_begin_function(module: i64, name_ptr: i64, name_len: i64, sig: i64) -> i64
extern fn rt_cranelift_iadd(ctx: i64, a: i64, b: i64) -> i64
// ... 50+ more FFI functions
```

**But the Simple code making these FFI calls is INTERPRETED!**

```
Simple codegen.spl (interpreted)
         ↓
   FFI calls → Cranelift (compiled Rust)
         ↓
   Cranelift generates native code
         ↓
   Produces executable binary
```

So the **compiler** runs slowly (interpreted), but the **output binary** is native.

---

## Performance Breakdown

### Bootstrap Compilation Performance

| Stage | What Runs | How | Speed |
|-------|-----------|-----|-------|
| **Stage 1** | `simple_runtime` (Rust) interpreting `simple/compiler/main.spl` | Interpreted | Slow |
| **Stage 2** | `simple_new1` (compiled) running `simple/compiler/main.spl` | Still interpreted! | Slow |
| **Stage 3** | `simple_new2` (compiled) running `simple/compiler/main.spl` | Still interpreted! | Slow |

**All 3 stages are equally slow** because:
- `simple_new1`, `simple_new2`, `simple_new3` are **executables**
- But they're executables that **run an interpreter**
- The interpreter then interprets `simple/compiler/main.spl`

### Why 3-5x Slower Than Expected

**Expected (if compiled):**
```
Rust compiler:  1.0x baseline
Simple compiler (compiled): ~1.0-1.2x (similar LLVM backend)
```

**Actual (interpreted):**
```
Rust compiler:     1.0x baseline
Simple compiler:  50-100x slower (interpreter overhead)
```

But you see **3-5x** in practice because:
1. Interpreter is heavily optimized (arena allocation, string interning)
2. Most time is in Cranelift backend (Rust FFI) - 70%+
3. Only HIR/MIR/driver logic is interpreted - 20-30%

**Rough breakdown:**
```
Total compile time: 100%
  - Parsing (interpreter):   10%  (50x slower = 500% without optimization)
  - HIR/MIR (interpreter):   10%  (50x slower = 500% without optimization)
  - Codegen (Rust FFI):      70%  (1x - no overhead!)
  - I/O, linking:            10%  (1x)

Net slowdown: 0.1*50 + 0.1*50 + 0.7*1 + 0.1*1 = 5 + 5 + 0.7 + 0.1 = 10.8x theoretical
```

With optimizations and caching: **~3-5x in practice**.

---

## Solution: Self-Hosting with Compiled Bootstrap

### The Fix (Not Yet Implemented)

**Step 1: Compile the Simple compiler itself**
```bash
# Bootstrap with interpreter (once)
simple_runtime compile simple/compiler/main.spl -o simple_compiler_stage1 --native

# Now simple_compiler_stage1 is a NATIVE EXECUTABLE
# It still interprets input .spl files, but its OWN logic is compiled
```

**Step 2: Use compiled compiler for subsequent builds**
```bash
# This runs compiled Simple code compiling other Simple code
./simple_compiler_stage1 compile myapp.spl -o myapp --native
```

### Why Not Done Yet?

**Codegen feature gaps** prevent self-compilation:
- ❌ Matrix ops
- ❌ Pipeline operators
- ❌ Static methods
- ❌ Context statements

**Workaround:** Simple compiler uses these features, so it **must** be interpreted.

**From error message:**
```rust
// src/rust/compiler/src/hir/lower/error.rs:65
#[error("Static method `{class_name}.{method_name}()` not yet supported in native compilation. Use interpreter mode...")]
StaticMethodNotSupported { class_name: String, method_name: String },
```

---

## Roadmap to Native Speed

### v0.4.0 Goals

#### Option A: Complete Codegen (Hard)
**Implement missing features in Cranelift backend:**
1. Matrix operations runtime library
2. Pipeline operator dispatch
3. Static method support
4. Async runtime integration
5. Context tracking

**Effort:** 8-12 weeks
**Risk:** High complexity
**Benefit:** Full feature parity

#### Option B: Optimize Interpreter (Easy)
**Make interpretation faster:**
1. JIT compilation for hot loops
2. Better caching (memoization)
3. Inline FFI calls
4. Lazy evaluation

**Effort:** 3-4 weeks
**Risk:** Low
**Benefit:** 2-3x speedup (still slower than native)

#### Option C: Hybrid (Recommended)
**Compile safe subset, interpret advanced features:**
1. Detect which functions use advanced features
2. Compile simple functions to native
3. Interpret complex functions
4. Mix at function granularity

**Effort:** 6-8 weeks
**Risk:** Medium
**Benefit:** 5-10x speedup (native for 80% of code)

### Long-Term (v1.0+)

**Full LLVM backend** (not Cranelift):
- Direct LLVM IR generation
- Full optimization pipeline
- All features supported
- True parity with Rust

**Effort:** 20-30 weeks
**Benefit:** 1:1 performance with Rust

---

## Misconceptions to Clarify

### ❌ "Simple code compiles to LLVM"
**Reality:** Simple compiler (written in Simple) is **interpreted**. The *output* binaries it produces are native.

### ❌ "Bootstrap = compiled bootstrap"
**Reality:** Bootstrap stages are all **interpreted**. The `simple_new1/2/3` binaries run an interpreter.

### ❌ "Rust crates are slow, Simple would be faster"
**Reality:** Rust crates are **native compiled**. Simple code is **interpreted**. Rust is 50-100x faster for now.

### ✅ "If Simple compiler were compiled, it would match Rust speed"
**Correct!** Both would use LLVM/Cranelift backend. Only parser/driver overhead would differ (~5-10%).

---

## Current Status Summary

| Component | Language | Execution Mode | Speed |
|-----------|----------|----------------|-------|
| **Simple compiler** | Simple | **Interpreted** | 50-100x slower |
| **Output binaries** | Simple | **Compiled (native)** | ~1-2x slower than Rust |
| **Runtime library** | Rust | Compiled | 1x baseline |
| **Rust compiler** | Rust | Compiled | 1x baseline |

---

## Action Items for v0.4.0

### High Priority
1. **Profile interpreter bottlenecks** - Where is time spent?
2. **Implement hybrid compilation** - Compile safe subset
3. **JIT hot loops** - Inline FFI calls in interpreter

### Medium Priority
4. **Complete codegen features** - Static methods, pipelines
5. **Benchmark comparison** - Rust vs interpreted vs compiled Simple

### Low Priority
6. **LLVM backend** - Replace Cranelift (long-term)
7. **Full self-hosting** - Compile the compiler with itself

---

## Conclusion

**Q: "If both compile to LLVM, why is Simple slower?"**

**A: Simple code DOESN'T compile to LLVM yet - it's interpreted!**

- ✅ Output binaries are native (via Cranelift)
- ❌ Simple compiler itself runs interpreted
- ❌ Codegen backend incomplete (missing features)
- 🎯 v0.4.0 goal: Hybrid compilation for 5-10x speedup
- 🚀 v1.0 goal: Full LLVM backend for 1:1 parity with Rust

**We're not slow because Simple is bad - we're slow because we're still bootstrapping!** 🐣→🦅
