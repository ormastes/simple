# LLVM Optimization Best Practices for Highly Optimized Binaries (2026)

**Research Date:** February 15, 2026
**Target:** Production-quality optimized binaries using LLVM/Clang
**LLVM Versions:** 17, 18, 19+

---

## Executive Summary

This document compiles best practices for producing highly optimized binaries using LLVM, covering optimization passes, PGO, LTO, auto-vectorization, interprocedural optimizations, machine-specific targeting, and LLVM IR emission strategies. Key findings:

- **PGO provides 7-20% speedups** across diverse workloads (browsers, compilers, large applications)
- **ThinLTO delivers 2.63% speedup** with only 1.2x compilation time overhead (vs 5x for full LTO)
- **x86-64-v3 (AVX2)** targeting can yield **4-11x speedups** in math-heavy code
- **Proper LLVM IR annotations** (nsw/nuw, TBAA, alignment) are critical for optimizer effectiveness
- **Loop vectorization** requires careful attention to dependency analysis and alias information

---

## 1. LLVM Optimization Passes: -O0 to -O3

### Optimization Level Overview

| Level | Purpose | Compile Time | Binary Size | Performance |
|-------|---------|--------------|-------------|-------------|
| `-O0` | No optimization | Fast | Largest | Slowest |
| `-O1` | Basic optimization | Moderate | Large | Basic |
| `-O2` | **Recommended** | Slower | Medium | Good |
| `-O3` | Aggressive speed | Slowest | Larger | Best (usually) |
| `-Os` | Size optimization | Moderate | Smallest | Variable |
| `-Oz` | Aggressive size | Moderate | Minimal | Lower |

### Key Differences

**-O2 (Balanced):**
- Standard production optimization level
- Includes most beneficial passes without excessive compile time
- Good code size vs performance tradeoff
- Enables interprocedural optimization (IPO) within object files

**-O3 (Aggressive Speed):**
- Like -O2 plus optimizations that may increase code size
- More aggressive loop optimizations (unrolling, vectorization)
- More inlining (can significantly increase binary size)
- Longer compile times
- **Not always faster** - increased I-cache pressure can hurt some workloads

**-Os (Size Priority):**
- Optimizes for code size while maintaining reasonable performance
- Progressive reduction in executable size from -O0 to -Oz
- Useful for embedded systems or cache-constrained environments

### Pass Complexity

At -O3 level in LLVM 10.0, there are **88 options** creating an enormous search space. Different option orders can produce varying optimization outcomes, leading to research on:
- Reinforcement learning for pass ordering
- Two-stage optimization methods for energy/performance
- Profile-guided pass selection

**Source:** [LLVM -O3 optimization passes](https://gist.github.com/minjang/89ee4cd6a040dfda0d7dc23603b3c8c3), [Compiling With Clang Optimization Flags](https://www.incredibuild.com/blog/compiling-with-clang-optimization-flags), [A Two-Stage LLVM Option Sequence Optimization Method](https://www.sciencedirect.com/science/article/abs/pii/S2210650224001299)

---

## 2. Profile-Guided Optimization (PGO)

### Overview

PGO uses runtime profiling data to inform compiler decisions, combining static analysis with actual execution behavior. It's one of the most impactful optimization techniques available.

### PGO Workflow (4 Steps)

```bash
# 1. Compile with instrumentation
clang++ -fprofile-generate -O2 myapp.cpp -o myapp_instrumented

# 2. Run instrumented program with representative workload
./myapp_instrumented < typical_input.txt
# Generates default_<id>.profraw files

# 3. Convert profile data
llvm-profdata merge -output=myapp.profdata default_*.profraw

# 4. Compile with profile data
clang++ -fprofile-use=myapp.profdata -O2 myapp.cpp -o myapp_optimized
```

### How PGO Works Internally

**Instrumentation Phase:**
- Lightweight counters inserted at AST or IR level
- Tracks: function entries, basic block visits, branch edges
- Minimal runtime overhead (typically <5% when properly tuned)

**Profile Usage Phase:**
- IR instructions annotated with branch-weight metadata
- Indirect call sites decorated with frequent targets and frequencies
- Optimizer uses this data for:
  - Better inlining decisions (hot paths get inlined)
  - Code layout optimization (hot blocks grouped together)
  - Register allocation prioritization
  - Devirtualization (virtual calls → direct calls on hot paths)

### Typical Speedup Results

| Application | Platform | Speedup | Source |
|-------------|----------|---------|--------|
| Chrome Browser | Windows | 7.3% | [Rust PGO Guide](https://doc.rust-lang.org/beta/rustc/profile-guided-optimization.html) |
| Firefox | General | 5% | [Rust PGO Guide](https://doc.rust-lang.org/beta/rustc/profile-guided-optimization.html) |
| Test Suite Example | Benchmark | 6.8% (avg 7.6%, σ=1.2%) | [From Profiling to Optimization](https://arxiv.org/html/2507.16649v1) |
| Clangd (LLVM indexer) | Indexing llvm-project | ~20% (10 min → 8 min) | [PGO optimization results](https://github.com/llvm/llvm-project/issues/63486) |
| Rust Compiler | ARM64/Linux | 10-20% across benchmarks | [How to speed up Rust compiler 2025](https://nnethercote.github.io/2025/03/19/how-to-speed-up-the-rust-compiler-in-march-2025.html) |
| Large code footprints | Various | "Double digit percentages not uncommon" | [Arm PGO & BOLT Results](https://www.phoronix.com/news/Arm-Fast-PGO-BOLT-LLVM-Clang) |

### Best Practices

1. **Representative workload is critical** - Profile must match production usage patterns
2. **SPE-driven PGO** (Statistical Performance Events) achieves >99% hotspot identification with <5% overhead
3. **Combine with BOLT** - Binary optimization can stack with PGO for additional gains
4. **Context-Sensitive PGO (CSPGO)** - Newer variant that considers call context, yields better results
5. **Multi-stage PGO** - Profile multiple workloads and merge for broader optimization

**Sources:** [Profile-guided Optimization (Rust Guide)](https://doc.rust-lang.org/beta/rustc/profile-guided-optimization.html), [From Profiling to Optimization](https://arxiv.org/html/2507.16649v1), [The many faces of LLVM PGO and FDO](https://aaupov.github.io/blog/2023/07/09/pgo), [Arm Shows Off Great Performance Results](https://www.phoronix.com/news/Arm-Fast-PGO-BOLT-LLVM-Clang)

---

## 3. Link-Time Optimization (LTO)

### Overview

LTO defers final code generation until link time when all modules are visible, enabling whole-program optimization. LLVM offers two modes: Full LTO and ThinLTO.

### Full LTO (Regular LTO)

**Mechanism:**
- Object files contain LLVM IR instead of machine code
- At link time, all IR combined into single massive module
- Interprocedural analysis runs on entire program
- Single-threaded processing

**Performance:**
- LLVM Clang 3.9: **2.86% average runtime improvement**
- Compilation time: **~5x non-LTO** (massive overhead)
- Memory usage: Very high for large codebases

**When to Use:**
- Small to medium codebases (<1M LOC)
- Release builds where compile time is acceptable
- Maximum optimization priority

### ThinLTO

**Mechanism:**
- Distributed compilation model
- At link time: builds lightweight global function index
- Each module optimized in **parallel** with selective cross-module inlining
- Function importing based on call graph analysis

**Performance:**
- LLVM Clang 3.9: **2.63% runtime improvement** (vs 2.86% for full LTO)
- Compilation time: **1.2x non-LTO** (only 20% overhead!)
- Near-linear scalability with core count

**When to Use:**
- Large codebases (>1M LOC)
- Development builds where fast iteration matters
- CI/CD pipelines with limited build time budgets

### Comparison Table

| Metric | Full LTO | ThinLTO | Winner |
|--------|----------|---------|--------|
| Runtime Speedup | 2.86% | 2.63% | Full LTO (slight) |
| Compile Time | 5.0x | 1.2x | **ThinLTO (4x faster)** |
| Memory Usage | Very High | Moderate | **ThinLTO** |
| Parallelism | Single-threaded | Multi-threaded | **ThinLTO** |
| Incrementality | Poor | Good | **ThinLTO** |

### Enabling LTO

```bash
# Full LTO
clang++ -flto -O2 file1.cpp file2.cpp -o output

# ThinLTO (recommended for most projects)
clang++ -flto=thin -O2 file1.cpp file2.cpp -o output

# With explicit parallelism
clang++ -flto=thin -O2 -Wl,--thinlto-jobs=8 file1.cpp file2.cpp -o output
```

### Best Practices

1. **Default to ThinLTO** unless you're chasing every last 0.2%
2. **Enable LTO at -O2 or higher** - IPO is limited without optimization
3. **Non-static functions require LTO** - within-object-file IPO can't optimize across boundaries
4. **Use with PGO** - LTO and PGO are complementary (stack the benefits)
5. **Watch link-time memory** - Full LTO can OOM on large projects

**Sources:** [ThinLTO: Scalable and Incremental LTO](https://news.ycombinator.com/item?id=11961621), [Link-time optimisation (LTO)](https://convolv.es/guides/lto/), [Link Time Optimizations: New Way](https://johnnysswlab.com/link-time-optimizations-new-way-to-do-compiler-optimizations/), [LLVM Link Time Optimization Design](https://rocm.docs.amd.com/projects/llvm-project/en/latest/LLVM/llvm/html/LinkTimeOptimization.html)

---

## 4. Auto-Vectorization

### Overview

LLVM's auto-vectorizers transform scalar code into SIMD vector operations (SSE, AVX, AVX2, AVX-512, NEON). Two vectorizers work together:

1. **Loop Vectorizer** - Widens instructions in loops to operate on multiple consecutive iterations
2. **SLP Vectorizer** - Merges multiple scalars found in code into vectors

### Vectorization Requirements

LLVM vectorizes when it can prove:

1. **Iterations are independent** - No loop-carried dependencies (except reductions)
2. **Memory accesses are well-behaved** - No aliasing surprises, predictable indexing
3. **Trip count handling** - Works with unknown iteration counts via scalar epilogue
4. **Non-power-of-2 counts** - Automatically inserts epilogue for remainder iterations

### Loop Patterns That Vectorize Well

```cpp
// Good: Simple independent loop
for (int i = 0; i < n; i++) {
    output[i] = input[i] * 2.0f;
}

// Good: Reduction (special handling)
float sum = 0.0f;
for (int i = 0; i < n; i++) {
    sum += array[i];
}

// Bad: Loop-carried dependency
for (int i = 1; i < n; i++) {
    array[i] = array[i-1] + 1;  // Depends on previous iteration
}
```

### What Prevents Vectorization

1. **Aliasing uncertainty** - Compiler can't prove input/output don't overlap
2. **Complex control flow** - Early exits, breaks, multiple nested conditions
3. **Function calls** - Unless inlined or provably pure
4. **Non-affine indexing** - `array[hash(i)]` instead of `array[i*stride]`
5. **Type punning** - Aliasing violations that can't be analyzed

### Enabling Better Vectorization

**1. Help Alias Analysis:**
```cpp
// Rust-style: separate input/output ensures no aliasing
void process(const float* __restrict__ input,
             float* __restrict__ output, size_t n);

// C++: restrict keyword tells compiler no aliasing
```

**2. Simplify Loop Structure:**
```cpp
// Before: Complex bounds
for (int i = start; i < end && check(i); i++)

// After: Hoist invariants
int limit = min(end, find_limit());
for (int i = start; i < limit; i++)
```

**3. Compiler Flags:**
```bash
# Force vectorization width (override cost model)
clang++ -mllvm -force-vector-width=8 -O3 code.cpp

# Target specific CPU for wider SIMD
clang++ -march=native -O3 code.cpp        # Use host CPU features
clang++ -march=x86-64-v3 -O3 code.cpp     # AVX2 (Haswell+)
clang++ -march=x86-64-v4 -O3 code.cpp     # AVX-512 (Skylake-X+)

# Optimization remarks (debugging)
clang++ -Rpass=loop-vectorize -O3 code.cpp              # What vectorized
clang++ -Rpass-missed=loop-vectorize -O3 code.cpp       # What didn't
clang++ -Rpass-analysis=loop-vectorize -O3 code.cpp     # Why it failed
```

**4. Profile-Guided Vectorization:**
- PGO provides trip count information → better vectorization decisions
- Hot loops get more aggressive vectorization

### Vectorization Cost Model

LLVM's vectorizer uses a cost model to decide:
- Whether to vectorize at all (overhead vs benefit)
- Optimal vector width (4-wide, 8-wide, 16-wide, etc.)
- Whether to unroll after vectorizing

**Cost factors:**
- Loop trip count (estimated or profiled)
- Memory access patterns (strided, gather/scatter)
- Arithmetic intensity
- Register pressure
- Target CPU capabilities

**Sources:** [Auto-Vectorization in LLVM](https://rocm.docs.amd.com/projects/llvm-project/en/latest/LLVM/llvm/html/Vectorizers.html), [LLVM and the automatic vectorization of loops](https://sc18.supercomputing.org/proceedings/workshops/workshop_files/ws_llvmf106s2-file1.pdf), [An introduction to auto-vectorization with LLVM](https://artagnon.com/compilers/intro-vec), [CS 6120: LLVM Loop Autovectorization](https://www.cs.cornell.edu/courses/cs6120/2019fa/blog/llvm-autovec/)

---

## 5. Interprocedural Optimizations (IPO)

### Overview

Interprocedural optimization analyzes entire programs rather than single functions, enabling transformations that cross function boundaries.

### Key IPO Techniques

#### 1. Inlining

**Why It's Critical:**
> "Inlining is considered by many (including important figures in the compiler community like Chandler Carruth) to be the single most important optimization in optimizing compilers."

**Benefits:**
- Eliminates call overhead
- Exposes optimization opportunities (constant propagation, dead code elimination)
- Enables more precise alias analysis
- Allows better register allocation across function boundaries

**Tradeoffs:**
- Code size increase (I-cache pressure)
- Compilation time increase
- Can hurt performance if overdone (-O3 risk)

**Heuristics:**
- Function size (small functions always inlined)
- Call frequency (hot functions prioritized via PGO)
- Caller context (constants passed as arguments)
- Inlining depth limit (prevent exponential explosion)

#### 2. Devirtualization

**What It Does:**
Converts indirect (virtual) calls to direct calls, enabling:
- Inlining of virtual methods
- Removal of vtable lookups
- Better branch prediction

**Mechanism:**
- Type propagation analysis determines exact type
- Virtual call replaced with direct call to known target
- Works best with final classes, sealed hierarchies, or PGO data

**LLVM Implementation:**
- Whole-program analysis at link time (requires LTO)
- Virtual pointer invariance modeling
- Class hierarchy analysis (CHA)

**Example:**
```cpp
// Before devirtualization
Base* obj = new Derived();
obj->virtual_method();  // Indirect call through vtable

// After devirtualization (if type known)
Derived* obj = new Derived();
obj->Derived::virtual_method();  // Direct call (can be inlined!)
```

#### 3. Argument Promotion

**What It Does:**
Promotes function arguments from pointers to direct values when safe.

**Example:**
```cpp
// Before
void process(Point* p) {
    return p->x + p->y;
}

// After (if caller always passes same struct)
void process(int x, int y) {
    return x + y;
}
```

**Benefits:**
- Eliminates memory loads
- Enables scalar optimizations (CSE, constant folding)
- Better register allocation

#### 4. Dead Argument Elimination

Removes unused function parameters when all callers are visible (whole-program analysis).

#### 5. Function Cloning

Creates specialized versions of functions for different calling contexts (similar to C++ template instantiation but automated).

### Enabling IPO

**GCC and Clang enable IPO by default at -O2**, but:
- Scope limited without LTO (only within object file)
- Non-static functions can't be eliminated without whole-program view
- Best results require `-flto` or `-flto=thin`

**Sources:** [What Happens If We Inline Everything?](https://sbaziotis.com/compilers/what-happens-if-we-inline-everything.html), [How LLVM Optimizes a Function](https://blog.regehr.org/archives/1603), [Devirtualization in LLVM](https://dl.acm.org/doi/abs/10.1145/3135932.3135947), [Interprocedural optimization - Wikipedia](https://en.wikipedia.org/wiki/Interprocedural_optimization)

---

## 6. Machine-Specific Optimizations

### x86-64 Microarchitecture Levels

AMD and Intel defined four x86-64 feature levels for standardized targeting:

| Level | Year | Key Features | Example CPUs |
|-------|------|--------------|--------------|
| **x86-64** | 2003 | SSE, SSE2 | Opteron, Pentium 4 |
| **x86-64-v2** | 2009 | + SSSE3, SSE4.1, SSE4.2, POPCNT | Nehalem, Bulldozer |
| **x86-64-v3** | 2013 | + AVX, AVX2, BMI1, BMI2, F16C, FMA, LZCNT, MOVBE | **Haswell+** ⭐ |
| **x86-64-v4** | 2017 | + AVX-512 (F, BW, CD, DQ, VL) | Skylake-X, Zen 4 |

### x86-64-v3 (AVX2): The Sweet Spot

**Why v3?**
- **Broad compatibility** - All post-2013 CPUs (Haswell, Ryzen 1000+)
- **Significant speedup** - 4-11x on math-heavy code
- **Production ready** - Linux distributions (Arch, RHEL 9) ship v3 builds
- **LLVM/GCC support** - Both support `-march=x86-64-v3` since 2020-2021

**Example Results (February 2026):**
> "With AVX2 targeting x86-64-v3, Oxygene compiler achieved noticeably faster performance than Visual C++ also targeting AVX2, demonstrating **4x to 11x speedups** in math-heavy VCL applications."

### Enabling Machine-Specific Optimization

```bash
# Use host CPU features (best for local builds)
clang++ -march=native -O3 code.cpp

# Target x86-64-v3 (recommended for distribution)
clang++ -march=x86-64-v3 -O3 code.cpp

# Target x86-64-v4 (AVX-512, if min target supports it)
clang++ -march=x86-64-v4 -O3 code.cpp

# Target specific CPU
clang++ -march=haswell -O3 code.cpp
clang++ -march=skylake -O3 code.cpp
clang++ -march=znver3 -O3 code.cpp  # Ryzen 5000
```

### Other Machine-Specific Features

**1. Branch Prediction Hints:**
```cpp
// LLVM builtin
if (__builtin_expect(rare_condition, 0)) {
    // Unlikely path
}

// C++20 standard
if (condition) [[likely]] {
    // Hot path
}
```

**2. Prefetching:**
```cpp
// Prefetch data into cache before use
__builtin_prefetch(&data[i+64]);  // Prefetch 64 elements ahead
```

**3. Cache Line Alignment:**
```cpp
// Align hot data structures to cache lines
struct alignas(64) HotStruct {
    // 64-byte alignment (typical cache line)
};
```

**Sources:** [GCC 11's x86-64 Microarchitecture Feature Levels](https://www.phoronix.com/news/GCC-11-x86-64-Feature-Levels), [New x86-64 micro-architecture levels](https://groups.google.com/g/llvm-dev/c/IINEIVmfbD8/m/SQKFpUo7AQAJ), [Your VCL App: 4x to 11x Faster Math Performance](https://blogs.remobjects.com/2026/02/09/your-vcl-app-faster-4x-to-11x-math-performance/), [RHEL 9 x86-64-v2 microarchitecture](https://developers.redhat.com/blog/2021/01/05/building-red-hat-enterprise-linux-9-for-the-x86-64-v2-microarchitecture-level)

---

## 7. LLVM IR Best Practices

### Overview

The quality of LLVM IR directly impacts optimization effectiveness. Well-formed IR with proper metadata enables more aggressive transformations.

### Critical IR Annotations

#### 1. nsw/nuw Flags (No Signed/Unsigned Wrap)

**What They Do:**
- `nsw`: No signed wrap - overflow produces poison (undefined behavior)
- `nuw`: No unsigned wrap - overflow produces poison

**Why They Matter:**
- Enable aggressive strength reduction
- Allow loop optimization (induction variable analysis)
- Improve alias analysis (e.g., GEP canonicalization)

**Example:**
```llvm
; Without flags (conservative)
%sum = add i32 %a, %b

; With flags (enables more optimization)
%sum = add nsw i32 %a, %b    ; Signed addition, no overflow
%prod = mul nuw i32 %x, %y   ; Unsigned multiply, no overflow
```

**When to Use:**
- C/C++: Signed integer overflow is UB → always use `nsw` for signed ops
- Loop indices: Usually `nsw` (array indices don't wrap in practice)
- Unsigned arithmetic: `nuw` when overflow impossible

**Caution:**
> "Mul reassociation in instcombine does not maintain NSW... impacting alias analysis negatively when canonicalizing GEP"

Ensure transformations preserve these flags or optimizer quality degrades.

#### 2. TBAA Metadata (Type-Based Alias Analysis)

**What It Does:**
Communicates pointer aliasing facts the optimizer can't deduce from IR alone.

**Why It Matters:**
- Enables aggressive code motion (hoisting loads out of loops)
- Allows reordering of memory operations
- Critical for vectorization (prove independence)

**Mechanism:**
```llvm
; Load from int* with TBAA tag
%val = load i32, i32* %ptr, !tbaa !1

; Store to float* with different TBAA tag
store float %f, float* %ptr2, !tbaa !2

; TBAA metadata nodes
!1 = !{!"int", !3}      ; int type
!2 = !{!"float", !3}    ; float type
!3 = !{!"simple-types"} ; Root
```

**Key Rules:**
- Removing TBAA is always safe (conservative: "aliases everything")
- Incorrect TBAA is UB (can cause miscompiles)
- Must match source language aliasing rules (C strict aliasing, Rust borrowing)

**Implementation Steps:**
1. Create TBAA root node for your type system
2. Create metadata for each type
3. Annotate all load/store instructions
4. Ensure hierarchy matches language semantics

#### 3. Alignment Metadata

**What It Does:**
Specifies pointer/data alignment stronger than type default.

**Why It Matters:**
- Enables vectorized memory operations (aligned loads are faster)
- Allows more aggressive optimizations (assume no unaligned access traps)
- Can eliminate runtime alignment checks

**Example:**
```llvm
; Load with explicit alignment
%val = load i32, i32* %ptr, align 16    ; 16-byte aligned (SIMD-friendly)

; Store with alignment
store float %f, float* %ptr, align 32   ; 32-byte aligned (AVX)

; Allocation with alignment
%ptr = alloca [100 x float], align 64   ; 64-byte aligned (cache line)
```

**Best Practices:**
- Heap allocations: Ensure allocator respects alignment (e.g., `aligned_alloc`)
- Stack allocations: Use `alloca` alignment attribute
- Global data: Use `alignas` / `__attribute__((aligned))`

#### 4. Function Attributes

**Key attributes for optimization:**
```llvm
; Pure function (no side effects, same output for same input)
declare i32 @compute(i32) readonly nounwind

; Function doesn't throw exceptions
define void @process() nounwind { ... }

; Function doesn't return
define void @abort() noreturn { ... }

; Function doesn't access memory
declare i32 @pure_math(i32) readnone

; Inlining hints
define void @hot_function() alwaysinline { ... }
define void @cold_function() noinline { ... }
```

### General IR Best Practices

**1. Canonicalization:**
- Use canonical forms (e.g., `icmp ult` instead of `icmp ugt` when possible)
- Simplifies pattern matching in optimization passes

**2. SSA Quality:**
- Minimize Phi nodes (use mem2reg pass)
- Keep SSA form clean (simplifies analysis)

**3. Metadata Preservation:**
- Ensure your IR transformations preserve metadata
- Use `IRBuilder` helpers to auto-attach metadata

**4. Debugging Metadata:**
- Even in release builds, some debug info helps optimizers
- Source locations enable better diagnostics

**Sources:** [Performance Tips for Frontend Authors](https://rocm.docs.amd.com/projects/llvm-project/en/latest/LLVM/llvm/html/Frontend/PerformanceTips.html), [LLVM Type Based Alias Analysis](https://the-ravi-programming-language.readthedocs.io/en/stable/llvm-tbaa.html), [LLVMdev: On semantics of add instruction - nsw,nuw flags](https://groups.google.com/g/llvm-dev/c/NvHZ5Nnqrfw), [A Gentle Introduction to LLVM IR](https://mcyoung.xyz/2023/08/01/llvm-ir/)

---

## 8. Modern LLVM Passes (LLVM 17-19)

### New Pass Manager (NPM)

**Status:** Default since LLVM 14, legacy pass manager removed in LLVM 17.

**Key Changes:**
- More granular pass scheduling
- Better pass interaction tracking
- Improved extensibility for custom passes
- Built-in pass pipelines: `PassBuilder::buildPerModuleDefaultPipeline()`

### Notable Optimization Passes

**LLVM 19 (September 2024):**

1. **Constant Argument to Global Variables Pass**
   - Converts constant arguments to global variables
   - Enables specialization of called functions
   - Example: `func(42)` → create `global_42`, specialize `func`

2. **IRNormalizer Pass**
   - Transforms modules to normal form
   - Reorders and renames instructions (preserves semantics)
   - Makes semantic diffing easier (comparing two IR modules)

3. **SPIR-V Backend**
   - Now official LLVM target (was experimental)
   - Enables OpenCL, SYCL, Vulkan, HLSL compilation
   - Relevant for GPU/compute workloads

**Earlier Notable Passes:**

1. **ConstraintElimination**
   - Eliminates unnecessary constraints in expressions
   - Uses range analysis and value tracking
   - Part of scalar optimization infrastructure

2. **LoopFlatten**
   - Flattens nested loops into single loop
   - Enables better vectorization and optimization
   - Example: `for(i) for(j) A[i][j]` → `for(k) A[k]`

3. **VectorCombine**
   - Combines vector operations for efficiency
   - Merges shuffles, extracts, inserts
   - Reduces vector operation overhead

4. **LoopVersioning**
   - Creates specialized loop versions based on runtime checks
   - Enables aggressive optimization in fast path

5. **NewGVN**
   - Global Value Numbering rewrite
   - More powerful than old GVN (finds more redundancies)

### Pass Pipeline Inspection

```bash
# Print optimization pipeline for -O2
clang++ -O2 -mllvm -print-pipeline-passes empty.cpp 2>&1 | head

# Example output (simplified):
# module(
#   function(
#     sroa,mem2reg,instcombine,simplifycfg,
#     loop-rotate,licm,indvars,loop-vectorize,
#     gvn,sccp,adce
#   ),
#   globaldce,constmerge
# )
```

### Debugging Pass Behavior

```bash
# Time each pass
clang++ -O3 -mllvm -time-passes code.cpp

# Print what each pass does
clang++ -O2 -mllvm -print-after-all code.cpp > passes.ll

# Bisect optimization regressions
clang++ -O3 -mllvm -opt-bisect-limit=100 code.cpp
```

**Sources:** [What Is New In LLVM 19?](https://developer.arm.com/community/arm-community-blogs/b/tools-software-ides-blog/posts/what-is-new-in-llvm-19), [LLVM 19.0.0git Release Notes](https://rocm.docs.amd.com/projects/llvm-project/en/latest/LLVM/llvm/html/ReleaseNotes.html), [Using the New Pass Manager](https://rocm.docs.amd.com/projects/llvm-project/en/develop/LLVM/llvm/html/NewPassManager.html), [CS 6120: A Loop Flattening Pass in LLVM](https://www.cs.cornell.edu/courses/cs6120/2020fa/blog/loop-flatten/), [LLVM's Analysis and Transform Passes](https://rocm.docs.amd.com/projects/llvm-project/en/develop/LLVM/llvm/html/Passes.html)

---

## 9. Optimization Workflow Recommendations

### Incremental Optimization Strategy

**Phase 1: Baseline**
```bash
clang++ -O2 -march=x86-64-v2 code.cpp -o binary_baseline
```
- Start with -O2 (good balance)
- Use conservative arch target (wide compatibility)

**Phase 2: Profile-Guided**
```bash
# Build instrumented
clang++ -O2 -march=x86-64-v2 -fprofile-generate code.cpp -o binary_pgo_gen

# Run representative workload
./binary_pgo_gen < production_data.txt

# Merge profiles
llvm-profdata merge -output=code.profdata default_*.profraw

# Build with profile
clang++ -O2 -march=x86-64-v2 -fprofile-use=code.profdata code.cpp -o binary_pgo
```
Expected: 5-20% speedup

**Phase 3: Add ThinLTO**
```bash
clang++ -O2 -march=x86-64-v2 -flto=thin -fprofile-use=code.profdata \
    code.cpp -o binary_pgo_lto
```
Expected: Additional 1-3% speedup

**Phase 4: Target Modern CPUs**
```bash
# For controlled deployment (v3 = 2013+ CPUs)
clang++ -O2 -march=x86-64-v3 -flto=thin -fprofile-use=code.profdata \
    code.cpp -o binary_optimized

# For internal use only
clang++ -O2 -march=native -flto=thin -fprofile-use=code.profdata \
    code.cpp -o binary_native
```
Expected: 4-11x on math-heavy code (varies widely)

**Phase 5: Experiment with -O3**
```bash
clang++ -O3 -march=x86-64-v3 -flto=thin -fprofile-use=code.profdata \
    code.cpp -o binary_o3
```
Expected: -5% to +10% (measure carefully!)

**Phase 6: BOLT (Post-Link Binary Optimizer)**
```bash
# Profile binary under load
perf record -e cycles:u -j any,u -o perf.data ./binary_optimized

# Convert perf data
perf2bolt binary_optimized -p perf.data -o binary_optimized.fdata

# Apply BOLT
llvm-bolt binary_optimized -o binary_bolted -data=binary_optimized.fdata \
    -reorder-blocks=ext-tsp -reorder-functions=hfsort -split-functions \
    -split-all-cold -dyno-stats
```
Expected: Additional 5-15% on large applications

### Verification at Each Step

```bash
# Performance testing
hyperfine --warmup 3 --runs 10 './binary_baseline' './binary_optimized'

# Correctness testing
./run_test_suite.sh binary_baseline > baseline.txt
./run_test_suite.sh binary_optimized > optimized.txt
diff baseline.txt optimized.txt  # Should be empty
```

### Common Pitfalls

1. **-O3 can hurt performance** - Measure, don't assume
2. **Unrepresentative PGO profiles** - Garbage in, garbage out
3. **Mixing optimization levels** - Use same flags for all TUs
4. **Ignoring compilation time** - Full LTO can kill CI/CD pipelines
5. **Over-optimizing cold code** - Focus on hot paths (use profiler)

---

## 10. Quick Reference Card

### Recommended Flags for Different Scenarios

**Development Build (fast iteration):**
```bash
clang++ -O0 -g code.cpp
```

**Release Build (general purpose):**
```bash
clang++ -O2 -march=x86-64-v2 -flto=thin code.cpp
```

**Performance-Critical (single binary):**
```bash
# Step 1: Profile
clang++ -O2 -march=x86-64-v3 -fprofile-generate code.cpp -o prof
./prof < workload.txt
llvm-profdata merge -output=code.profdata default_*.profraw

# Step 2: Optimize
clang++ -O2 -march=x86-64-v3 -flto=thin \
    -fprofile-use=code.profdata code.cpp -o release
```

**Embedded/Size-Constrained:**
```bash
clang++ -Os -flto=thin code.cpp
```

**Maximum Performance (no holds barred):**
```bash
# With PGO, ThinLTO, aggressive targeting
clang++ -O3 -march=native -flto=thin \
    -fprofile-use=code.profdata \
    -ffast-math \          # If FP precision not critical
    -fno-exceptions \       # If exceptions not used
    -fno-rtti \             # If RTTI not needed
    code.cpp -o max_perf
```

### Key Metrics to Track

| Metric | Tool | Target |
|--------|------|--------|
| Runtime Performance | hyperfine, perf | Faster |
| Binary Size | size, bloaty | Smaller (or acceptable) |
| Compilation Time | time | Under CI budget |
| I-cache Misses | perf stat -e L1-icache-load-misses | Lower |
| Branch Mispredictions | perf stat -e branch-misses | Lower |

### Troubleshooting Optimization Issues

**Performance Regression:**
```bash
# Bisect which optimization caused it
clang++ -O3 -mllvm -opt-bisect-limit=N code.cpp
# Binary search for problematic pass
```

**Vectorization Failure:**
```bash
# Find out why loop didn't vectorize
clang++ -O3 -Rpass-missed=loop-vectorize -Rpass-analysis=loop-vectorize code.cpp
```

**LTO Memory Issues:**
```bash
# Use ThinLTO instead of full LTO
clang++ -flto=thin ...  # Much lower memory usage

# Limit ThinLTO parallelism
clang++ -flto=thin -Wl,--thinlto-jobs=4 ...
```

---

## Summary: Expected Performance Gains

| Optimization | Typical Speedup | Compilation Time | When to Use |
|--------------|-----------------|------------------|-------------|
| -O2 vs -O0 | 3-10x | 2-5x | Always (baseline) |
| -O3 vs -O2 | -5% to +10% | 1.5-2x | Measure first |
| PGO | 5-20% | 1.5x (two builds) | Production binaries |
| ThinLTO | 2-3% | 1.2x | Large projects |
| Full LTO | 2.5-3% | 5x | Small projects only |
| x86-64-v3 (AVX2) | 1.5-11x (varies!) | ~1x | If min target = 2013+ |
| BOLT | 5-15% | Separate step | Very large apps |
| **All Combined** | **20-50%+** | Depends | High-value targets |

**Bottom Line:**
- **Start with:** `-O2 -march=x86-64-v3 -flto=thin`
- **Add PGO for:** 7-20% boost (highest ROI)
- **Consider -O3 only if:** measured improvement > code size cost
- **Use Full LTO only if:** project is small or build time unlimited
- **Profile everything** - Never optimize without data

---

## References

All source links embedded inline throughout document. Key categories:

- **LLVM Official Docs:** [Performance Tips](https://rocm.docs.amd.com/projects/llvm-project/en/latest/LLVM/llvm/html/Frontend/PerformanceTips.html), [Auto-Vectorization](https://rocm.docs.amd.com/projects/llvm-project/en/latest/LLVM/llvm/html/Vectorizers.html), [LTO Design](https://rocm.docs.amd.com/projects/llvm-project/en/latest/LLVM/llvm/html/LinkTimeOptimization.html)
- **Benchmarks:** [Phoronix](https://www.phoronix.com/), [Arm PGO Results](https://www.phoronix.com/news/Arm-Fast-PGO-BOLT-LLVM-Clang)
- **Tutorials:** [Johnny's Software Lab](https://johnnysswlab.com/), [Cornell CS 6120](https://www.cs.cornell.edu/courses/cs6120/)
- **Academic:** [ArXiv](https://arxiv.org/html/2507.16649v1), [ACM](https://dl.acm.org/doi/abs/10.1145/3135932.3135947)

**Document Version:** 1.0
**Last Updated:** February 15, 2026
**Next Review:** June 2026 (after LLVM 20 release)
