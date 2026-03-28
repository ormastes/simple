# Pure Simple Bootstrap Plan

## Analysis: Current State

### The Core Problem

The bootstrap binary (`bin/release/simple`, 33MB ELF) has a **broken `compile` command**:

```
SIMPLE_COMPILE_RUST=1 bin/release/simple compile src/app/cli/main.spl -o output.smf
→ error: rt_cli_handle_compile is not supported in interpreter mode
→ Produces 219-byte stub SMF (contains only: SMF header + "code" section + "main" symbol + `ret` instruction)
```

**Every binary tested** (bootstrap, v0.5.0 release, v0.5.0-rc.1 native ELF) produces the same 219-byte stubs. No available binary can actually compile Simple source to a working executable via `rt_cli_handle_compile`.

### What Actually Works

| Path | Status | Output | Limitation |
|------|--------|--------|------------|
| `native.spl` (Simple→C→gcc) | **WORKS** | Real 8-9KB ELF binaries | ~20 statement types only |
| `llvm_direct.spl` (Simple→C→clang→LLVM) | **WORKS** | Real ELF binaries, optimized | Same C codegen limitation |
| `rt_cli_handle_compile` (Cranelift) | **BROKEN** | 219-byte stubs | Always errors in interpreter mode |
| `compile` CLI command | **BROKEN** | Delegates to `rt_cli_handle_compile` | Same |


**Supported:**
- `fn` definitions + calls (with typed params, return types)
- `val`/`var` declarations (i64, text, bool, arrays)
- `if`/`elif`/`else`, `while`, `for..in range()`, `for..in array`
- `match`/`case` (string/integer only)
- `print` with string interpolation `"{var}"`
- Arrays `[1,2,3]`, indexing `arr[i]`, `.len()` → `_len`
- `break`, `continue`, `return`
- Compound assignment `+=`, `-=`, `*=`, `/=`

**NOT Supported (needed for CLI):**
- `struct` / `class` / `enum` definitions
- `use` / `import` (module system)
- String methods: `.contains()`, `.starts_with()`, `.substring()`, `.split()`, `.trim()`, `.replace()`, `.index_of()`
- `nil` / Option types
- `extern fn` declarations
- Closures / lambdas
- Method calls (`obj.method()`)
- `self` keyword
- `impl` blocks
- `static fn`
- `match` with enum variants
- Array methods: `.push()`, `.pop()`, `.join()`, `.merge()`
- `??` (null coalescing), `?.` (optional chaining)

### Bootstrap Process (current, broken)

```
Stage 1: Copy bin/release/simple → build/bootstrap/simple_new1
Stage 2: SIMPLE_COMPILE_RUST=1 simple_new1 compile main.spl → simple_new2.smf (219 bytes!)
Stage 3: SIMPLE_COMPILE_RUST=1 bootstrap simple_new2.smf compile main.spl → simple_new3.smf (fails!)
```

Stage 2 "succeeds" (exit code 0) but produces a useless 219-byte stub.
Stage 3 fails because the 219-byte stub can't be loaded as a valid SMF module.

---

## Plan: Pure Simple Self-Hosting Bootstrap

### Strategy: Incremental C Codegen Enhancement


### Phase 1: Enhanced C Codegen (c_codegen_v2.spl)

**Goal:** Support enough Simple features to compile a mini-compiler that can compile the full CLI.

**New features to add to C codegen:**

1. **Structs** → C structs
   ```simple
   struct Point:       →  typedef struct { long x; long y; } Point;
       x: i64
       y: i64
   ```

2. **String operations** → C string library calls
   ```simple
   s.len()             →  strlen(s)
   s.contains("x")     →  (strstr(s, "x") != NULL)
   s.starts_with("x")  →  (strncmp(s, "x", strlen("x")) == 0)
   s.substring(a, b)   →  simple_substring(s, a, b)  # helper fn
   s.split(",")         →  simple_split(s, ",")        # helper fn
   s.trim()             →  simple_trim(s)              # helper fn
   s.replace(a, b)      →  simple_replace(s, a, b)     # helper fn
   s.index_of("x")      →  simple_index_of(s, "x")     # helper fn
   ```

3. **Module inlining** → Resolve `use` at codegen time
   ```simple
   use compiler.backend.c_codegen_adapter (shared Codegen interface path)
   ```

4. **Enums** → C enums + tagged unions
   ```simple
   enum Color:         →  typedef enum { Color_Red, Color_Green } Color;
       Red
       Green
   ```

5. **Nil/Option** → NULL pointers
   ```simple
   var x = nil         →  void* x = NULL;
   if x != nil:        →  if (x != NULL) {
   ```

6. **Array methods** → Helper functions
   ```simple
   arr.push(x)         →  simple_array_push(&arr, &arr_len, x)
   arr.join(", ")      →  simple_join(arr, arr_len, ", ")
   ```

### Phase 2: Mini-Compiler (bootstrap_compiler.spl)

**Goal:** Write a minimal compiler using ONLY features from Phase 1's enhanced C codegen. This compiler compiles Simple→C with full feature support.

The mini-compiler would:
1. Parse Simple source (line-by-line, like current MIR C backend but more complete)
2. Resolve module imports (inline referenced functions)
3. Generate C code for ALL Simple features
4. Invoke gcc to produce native binary

**Size estimate:** ~2000-3000 lines of Simple code
**Feature subset used:** Only what Phase 1 C codegen supports

### Phase 3: Self-Hosting Bootstrap Pipeline

```
Step 1: bin/release/simple (interpreter) runs native.spl
        to compile bootstrap_compiler.spl → bootstrap_compiler (native ELF)

Step 2: ./bootstrap_compiler compiles src/app/cli/main.spl → simple_stage2 (native ELF)

Step 3: ./simple_stage2 compiles src/app/cli/main.spl → simple_stage3 (native ELF)

Verify: SHA256(stage2) == SHA256(stage3) → reproducible!
```

### Phase 4: Integration

1. Replace broken `rt_cli_handle_compile` with pure Simple compilation path
2. Update `cli_compile()` to use enhanced C codegen → gcc instead of FFI
3. Keep Cranelift available as optional backend for users who have it
4. Update bootstrap.spl to use new pipeline

### Alternative: Quick Fix (if feasible)

Instead of enhancing C codegen, check if:
1. An older version of the bootstrap binary has working `compile` (git history)
2. The Rust source exists in git history to rebuild a working binary
3. The 33MB binary has compile capability that's disabled by a config flag

---

## Implementation Order

```
Week 1: Phase 1 - Enhanced C codegen
  - String helper library (C runtime support)
  - Struct/enum support
  - Module inlining (use → inline)
  - Test with progressively complex programs

Week 2: Phase 2 - Mini-compiler
  - Write bootstrap_compiler.spl using Phase 1 features
  - Full Simple parser (line-based, ~800 lines)
  - Complete C codegen (~1200 lines)
  - Test: compile native.spl itself

Week 3: Phase 3 - Self-hosting
  - Bootstrap pipeline: interpreter → mini-compiler → CLI → CLI
  - Verification (hash comparison)
  - Integration with build system

Week 4: Phase 4 - Polish
  - CLI integration
  - Documentation
  - CI pipeline update
```

## Risk Assessment

| Risk | Impact | Mitigation |
|------|--------|------------|
| C codegen too limited for mini-compiler | High | Keep mini-compiler simple, use only basic features |
| String operations in C fragile | Medium | Extensive testing, use well-tested C string libs |
| Module resolution complex | Medium | Start with simple inlining, no circular deps |
| Performance regression | Low | C→gcc produces fast native code |
| Cranelift hang bug still present | Low | New pipeline avoids Cranelift entirely for bootstrap |

## Files to Create/Modify

| File | Action | Description |
|------|--------|-------------|
| `src/app/compile/c_codegen_v2.spl` | CREATE | Enhanced C code generator |
| `src/app/compile/c_runtime.h` | CREATE | C helper functions (string ops, arrays) |
| `src/app/compile/module_resolver.spl` | CREATE | Module import → inline resolver |
| `src/app/compile/bootstrap_compiler.spl` | CREATE | Mini-compiler for bootstrap |
| `src/app/build/bootstrap.spl` | MODIFY | Use new compilation pipeline |
| `src/app/io/mod.spl` | MODIFY | Update cli_compile to use pure Simple path |
| `test/compiler/c_codegen_v2_spec.spl` | CREATE | Tests for enhanced codegen |
