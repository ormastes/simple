# Plan: Build Full Simple Compiler from Core Simple

## Current Status

### ✅ Completed
- **Enum/Type Alignment**: All 375 compiler_core files align with seed.cpp
- **Transpilation**: Successfully generates 20,005 lines of C++
- **Types Proof**: 3-file minimal bootstrap compiles and runs perfectly

### ❌ Blockers
- **seed_cpp bugs**: ~20 C++ compilation errors (transpiler issues)
- **Err()/Ok() usage**: Result types not available in seed.cpp runtime

## Strategy: Three-Phase Approach

### Phase 1: Fix seed_cpp Transpiler Bugs (C++ Work)

**Goal**: Fix the ~20 C++ generation bugs in seed_cpp

**Required Fixes**:
1. **Function signature mismatches** - BackendFactory__create_specific
2. **Malformed syntax** - `expected ')'`, undeclared identifiers
3. **Type conversion errors** - pointer vs value confusion
4. **Return type handling** - void vs int64_t mismatches

**Effort**: 2-3 days of C++ debugging

**Files to Fix**: `seed/seed.c` or `seed/seed_cpp.c`

**Approach**:
```bash
# Debug seed_cpp to fix transpilation bugs
cd seed/
# Fix syntax generation bugs
# Fix type conversion logic
# Fix return statement generation
```

---

### Phase 2: Remove Result Type Dependencies (Simple Work)

**Goal**: Eliminate all Err()/Ok() usage from compiler_core

**Current Usage**:
- Minimal bootstrap: Already excluded via directory filters
- Full compiler_core: Would need refactoring

**Approach**:
1. Replace `Result<T>` with `Option<T>` or error flags
2. Use pattern: `var error: Option<text> = nil`
3. Check error after each operation

**Example Refactor**:
```simple
# Before (not available in seed.cpp):
fn parse(text: text) -> Result<Ast, text>:
    if invalid:
        return Err("parse error")
    Ok(ast)

# After (seed.cpp compatible):
struct ParseResult:
    ast: Ast
    error: text  # empty string = success

fn parse(text: text) -> ParseResult:
    if invalid:
        return ParseResult(ast: nil_ast(), error: "parse error")
    ParseResult(ast: ast, error: "")
```

**Effort**: 1-2 weeks (669 Err() usages in src/compiler/)

**Alternative**: Use the existing Simple compiler (bin/release/simple) to build compiler_core with full Result support

---

### Phase 3: Bootstrap Build Pipeline

**Goal**: Create a working compiler from compiler_core

**Option A: seed_cpp Path (After Phase 1+2)**
```bash
# Once seed_cpp bugs are fixed and Result types removed:
./seed/build/seed_cpp src/compiler_core/**/*.spl > bootstrap.cpp
clang++ bootstrap.cpp -o simple_compiler
./simple_compiler --version  # Success!
```

**Option B: Existing Compiler Path (Immediate)**
```bash
# Use the working Simple compiler to build compiler_core:
bin/release/simple compile src/compiler_core/main.spl -o build/core_compiler

# This works if compiler_core/main.spl has a proper CLI interface
```

**Option C: Hybrid Path (Best)**
```bash
# 1. Use existing Simple to compile a minimal working subset
bin/release/simple compile src/compiler_core/minimal_cli.spl -o build/stage1

# 2. Use stage1 to compile more of compiler_core
./build/stage1 compile src/compiler_core/main.spl -o build/stage2

# 3. Use stage2 to compile the full compiler_core
./build/stage2 compile src/compiler_core/*.spl -o build/full_compiler

# 4. Validate self-hosting
./build/full_compiler compile src/compiler_core/*.spl -o build/full_compiler_v2
diff build/full_compiler build/full_compiler_v2  # Should be identical
```

---

## Recommended Action: Option B (Immediate Win)

**Steps**:

1. **Create compiler_core CLI wrapper**:
```simple
# src/compiler_core/cli_main.spl
use driver.*
use backend.*

fn main():
    val args = parse_cli_args()
    val result = compile_file(args.input, args.output)
    match result:
        case CompileSuccess: 0
        case CompileError(msg):
            print("Error: {msg}")
            1
```

2. **Build with existing compiler**:
```bash
bin/release/simple compile src/compiler_core/cli_main.spl -o build/core_compiler
```

3. **Test the compiler**:
```bash
./build/core_compiler test.spl -o test
./test  # Run compiled output
```

4. **Self-host test**:
```bash
./build/core_compiler src/compiler_core/cli_main.spl -o build/core_compiler_v2
diff build/core_compiler build/core_compiler_v2
```

---

## Success Criteria

✅ **Immediate Success** (Option B):
- compiler_core compiles with bin/release/simple
- Produces working binary
- Can compile Simple programs
- Self-hosting validated

✅ **Complete Success** (Option A or C):
- seed_cpp bugs fixed OR multi-stage bootstrap works
- compiler_core fully self-hosting
- No dependency on bin/release/simple
- All 375 files compile cleanly

---

## Next Steps

**Recommended**: Try Option B first (use existing compiler)

```bash
# 1. Check if compiler_core has a CLI entry point
ls -la src/compiler_core/*main*.spl

# 2. Try compiling it
bin/release/simple compile src/compiler_core/bootstrap_main.spl -o build/test_core

# 3. If successful, create proper CLI wrapper
# 4. Build and validate
```

**Alternative**: Fix seed_cpp bugs (Phase 1)
- Requires C/C++ work on seed compiler
- Higher effort but cleaner long-term solution

**Fallback**: Document current state as "proof of concept"
- Types-only bootstrap proves enum fixes work
- Full transpilation validates all 375 files
- seed_cpp bugs are documented limitation
