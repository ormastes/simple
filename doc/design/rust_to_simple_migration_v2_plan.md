# Rust to Simple Migration Plan v2 - Test-First Approach

**Date:** 2026-01-30
**Version:** 0.4.0 Planning
**Strategy:** Write SSpec tests first, then port Rust → Simple with verification

---

## Core Principle: Test-First Migration

**Every Rust function/module gets SSpec tests BEFORE porting to Simple**

```
1. Analyze Rust code → Extract behavior
2. Write comprehensive SSpec tests (100% coverage goal)
3. Run tests against Rust implementation (baseline)
4. Port to Simple (interpreter + SMF + native)
5. Run same SSpec tests → Verify parity
6. Only after 100% pass: Replace Rust with Simple
```

---

## Migration Requirements

### Simple Must Support 3 Modes

**All ported code must work in:**

1. **Interpreter Mode** - Tree-walking, all features
2. **SMF Mode** - Compiled .smf binary
3. **Native Mode** - AOT compiled executable

**Test in all 3 modes:**
```bash
# Test interpreter
simple test path/to/spec.spl

# Test SMF
simple compile spec.spl -o spec.smf
simple spec.smf

# Test native
simple compile spec.spl -o spec --native
./spec
```

---

## What Can Be Ported (Excludes FFI/Unsafe)

### Layer Analysis

**✅ CAN PORT (Pure Logic):**
- Parser utilities (string processing, AST manipulation)
- Type checking algorithms (HM inference, constraint solving)
- Dependency resolution (graph algorithms)
- Package management (manifest parsing, version resolution)
- Diagnostics (error formatting, i18n)
- SDN parser (already has Simple version)
- LSP/DAP protocol handlers (message processing)
- Testing infrastructure (test runner, coverage analysis)
- CLI utilities (argument parsing, command dispatch)

**❌ CANNOT PORT (FFI/Unsafe/Hardware):**
- GC implementation (unsafe memory management)
- Runtime value representation (tagged pointers, unsafe)
- Cranelift/LLVM FFI bindings (external C/C++ libraries)
- Native library loader (libloading, dlopen/dlsym)
- SIMD intrinsics (platform-specific asm)
- GPU APIs (CUDA/ROCm FFI)
- Embedded bare-metal (no_std, startup code)
- WASM runtime (Wasmer FFI)
- Arena allocators (unsafe pointer manipulation)
- String interning (unsafe lifetime management)

**🟡 BRIDGE WITH FFI (Keep thin Rust wrapper):**
- Rust libraries we download: Keep Rust wrapper, call from Simple
  - `lasso` - String interning → Thin Rust FFI wrapper
  - `typed-arena` - Arena allocation → Thin Rust FFI wrapper
  - `memmap2` - Memory mapping → Thin Rust FFI wrapper
  - `cranelift-*` - Codegen backend → Already FFI
  - `tokio` - Async runtime → Thin Rust FFI wrapper
  - etc.

---

## Migration Phases (Bottom-Up)

### Phase 1: Pure Algorithm Crates (4-6 weeks)

**Target:** Zero-dependency logic, easiest to port and test

#### 1.1 SDN Parser (Week 1)
**Rust:** `src/rust/sdn/` (~2,000 lines)
**Simple:** Already exists in `src/app/sdn/` (partial)
**Status:** Complete Simple version, add SSpec tests

**SSpec Test Plan:**
```spl
# simple/std_lib/test/features/sdn_parser_spec.spl

feature "SDN Parser - Value Parsing":
    scenario "Parse integers":
        given:
            val input = "count: 42"
        when:
            val result = sdn.parse(input)
        then:
            result.get("count") == 42

    scenario "Parse nested structures":
        given:
            val input = """
                person:
                    name: Alice
                    age: 30
            """
        when:
            val result = sdn.parse(input)
        then:
            result.get("person").get("name") == "Alice"
            result.get("person").get("age") == 30

    scenario "Parse arrays":
        # ... 50+ scenarios for edge cases

feature "SDN Parser - Error Handling":
    scenario "Invalid syntax":
        # Test all error cases

feature "SDN Parser - Table Format":
    scenario "Parse table with columns":
        # Test SDN table format
```

**Coverage Goal:** 100% of Rust test cases + edge cases
**Verification:** Run against both Rust and Simple implementations

#### 1.2 Dependency Tracker (Week 2)
**Rust:** `src/rust/dependency_tracker/` (~1,500 lines)
**Purpose:** Module resolution, visibility, dependency graphs

**SSpec Test Plan:**
```spl
# simple/std_lib/test/features/dependency_resolution_spec.spl

feature "Module Resolution":
    scenario "Resolve absolute imports":
        given:
            val module = "use std.collections.List"
        when:
            val resolved = resolve_import(module)
        then:
            resolved.path == "std/collections.spl"
            resolved.item == "List"

    scenario "Resolve relative imports":
        # Test ../foo, ./bar patterns

    scenario "Resolve wildcard imports":
        # Test use foo.*

feature "Dependency Graph":
    scenario "Build dependency DAG":
        # Test cycle detection

    scenario "Topological sort":
        # Test compilation order

feature "Visibility Rules":
    scenario "Public vs private":
        # Test pub keyword enforcement
```

**Coverage:** 100% graph algorithms, all import patterns
**Modes:** Interpreter + SMF + Native (graph algorithms pure logic)

#### 1.3 Diagnostics Formatting (Week 3)
**Rust:** `src/rust/diagnostics/` (~1,000 lines)
**Purpose:** Error/warning messages, i18n

**SSpec Test Plan:**
```spl
# simple/std_lib/test/features/diagnostics_spec.spl

feature "Error Formatting":
    scenario "Format simple error":
        given:
            val error = Diagnostic(
                severity: Error,
                message: "undefined variable",
                span: Span(line: 42, col: 10)
            )
        when:
            val formatted = format_diagnostic(error)
        then:
            formatted.contains("line 42")
            formatted.contains("undefined variable")

    scenario "Format with code snippet":
        # Test context lines, highlighting

    scenario "Multiple labels":
        # Test compound errors

feature "I18n Support":
    scenario "Translate messages":
        # Test English, Japanese, Korean, etc.
```

**Coverage:** All diagnostic types, all i18n catalogs
**Modes:** All 3 (pure string processing)

---

### Phase 2: Package & Build Tools (6-8 weeks)

#### 2.1 Package Manager (Weeks 4-6)
**Rust:** `src/rust/pkg/` (~3,000 lines)
**Purpose:** Manifest parsing, dependency resolution, caching

**SSpec Test Plan:**
```spl
# simple/std_lib/test/features/package_manager_spec.spl

feature "Manifest Parsing":
    scenario "Parse simple.sdn manifest":
        given:
            val manifest = """
                package:
                    name: myapp
                    version: 1.0.0
                dependencies:
                    http: 2.0
                    json: 1.5
            """
        when:
            val parsed = parse_manifest(manifest)
        then:
            parsed.name == "myapp"
            parsed.version == Version(1, 0, 0)
            parsed.dependencies.len() == 2

feature "Dependency Resolution":
    scenario "Resolve semantic versions":
        # Test semver constraints

    scenario "Resolve conflicts":
        # Test version conflict resolution

    scenario "Detect cycles":
        # Test circular dependency detection

feature "Lock File":
    scenario "Generate lock file":
        # Test deterministic resolution

    scenario "Upgrade dependencies":
        # Test upgrade strategies

feature "Cache Management":
    scenario "Cache downloaded packages":
        # Test local cache

    scenario "Verify checksums":
        # Test integrity checks
```

**Coverage:** 100% resolver algorithms, all manifest formats
**Modes:** All 3 (algorithms + file I/O via FFI)
**FFI Bridge:** File I/O only (keep Rust fs:: wrapper)

#### 2.2 Build System (Weeks 7-8)
**Rust:** Various modules in `src/rust/driver/`
**Purpose:** Build orchestration, incremental compilation

**SSpec Test Plan:**
```spl
# simple/std_lib/test/features/build_system_spec.spl

feature "Incremental Build":
    scenario "Detect changed files":
        # Test hash-based change detection

    scenario "Rebuild minimal set":
        # Test dependency-aware rebuild

feature "Build Cache":
    scenario "Cache compiled modules":
        # Test .smf caching

feature "Parallel Build":
    scenario "Build independent modules in parallel":
        # Test parallelization
```

**Coverage:** All build strategies, cache invalidation
**Modes:** All 3

---

### Phase 3: Development Tools (8-10 weeks)

#### 3.1 LSP Server (Weeks 9-11)
**Rust:** `src/rust/lsp/` (~5,000 lines)
**Simple:** Already exists in `src/app/lsp/` (partial)
**Purpose:** IDE integration

**SSpec Test Plan:**
```spl
# simple/std_lib/test/features/lsp_spec.spl

feature "LSP Protocol":
    scenario "Initialize":
        given:
            val init_msg = lsp_initialize_request()
        when:
            val response = lsp_server.handle(init_msg)
        then:
            response.capabilities.textDocumentSync.? == true

    scenario "Go to definition":
        given:
            val source = "val x = 42\nprint x"
            val cursor = Position(line: 1, col: 6)  # on "x"
        when:
            val result = lsp_server.definition(source, cursor)
        then:
            result.location.line == 0
            result.location.col == 4

feature "Diagnostics":
    scenario "Report errors on change":
        # Test incremental diagnostics

feature "Completion":
    scenario "Complete symbols":
        # Test autocomplete

feature "Hover":
    scenario "Show type info":
        # Test hover tooltips
```

**Coverage:** All LSP message types, protocol compliance
**Modes:** Interpreter + Native (LSP runs as daemon)
**FFI Bridge:** JSON-RPC via existing runtime functions

#### 3.2 DAP Server (Weeks 12-13)
**Rust:** `src/rust/dap/` (~3,000 lines)
**Simple:** Already exists in `src/app/dap/` (partial)

**SSpec Test Plan:**
```spl
# simple/std_lib/test/features/dap_spec.spl

feature "DAP Protocol":
    scenario "Set breakpoint":
        # Test breakpoint handling

    scenario "Step through code":
        # Test stepping

    scenario "Inspect variables":
        # Test variable inspection
```

**Coverage:** All DAP message types
**Modes:** Interpreter + Native

#### 3.3 Formatter & Linter (Weeks 14-16)
**Rust:** Parts of `src/rust/compiler/` (formatter, lint)
**Simple:** Already exists in `src/app/formatter/`, `src/app/lint/`

**SSpec Test Plan:**
```spl
# simple/std_lib/test/features/formatter_spec.spl

feature "Code Formatting":
    scenario "Format indentation":
        given:
            val input = "fn foo():x=1\ny=2"
        when:
            val formatted = format_code(input)
        then:
            formatted == "fn foo():\n    x = 1\n    y = 2"

    scenario "Preserve comments":
        # Test comment preservation

    scenario "Format long lines":
        # Test line wrapping
```

**Coverage:** All AST node types, formatting rules
**Modes:** All 3

---

### Phase 4: Type System & Analysis (10-12 weeks)

#### 4.1 Type Checking (Weeks 17-20)
**Rust:** `src/rust/compiler/src/type_check/` (complex)
**Simple:** Already exists in `simple/compiler/type_infer.spl` (partial)

**SSpec Test Plan:**
```spl
# simple/std_lib/test/features/type_inference_spec.spl

feature "Hindley-Milner Inference":
    scenario "Infer function types":
        given:
            val code = "fn double(x): x * 2"
        when:
            val inferred = infer_type(code)
        then:
            inferred == "fn(Int) -> Int"

    scenario "Infer generic types":
        given:
            val code = "fn id(x): x"
        when:
            val inferred = infer_type(code)
        then:
            inferred == "fn<T>(T) -> T"

    scenario "Unify types":
        # Test unification algorithm

    scenario "Generalize types":
        # Test let-polymorphism

feature "Type Errors":
    scenario "Report type mismatches":
        given:
            val code = "val x: Int = \"hello\""
        when:
            val result = type_check(code)
        then:
            result.errors.len() > 0
            result.errors[0].message.contains("type mismatch")
```

**Coverage:** All type inference rules, edge cases
**Modes:** All 3 (pure algorithms)
**Complexity:** High - requires extensive testing

#### 4.2 Constraint Solving (Weeks 21-22)
**Rust:** Type constraint solver
**Simple:** Exists in type_infer.spl

**SSpec Test Plan:**
```spl
# simple/std_lib/test/features/constraint_solver_spec.spl

feature "Constraint Generation":
    scenario "Generate constraints from expressions":
        # Test constraint collection

feature "Constraint Solving":
    scenario "Solve linear constraints":
        # Test unification-based solving

    scenario "Detect unsolvable constraints":
        # Test error reporting
```

**Coverage:** All constraint types
**Modes:** All 3

---

### Phase 5: Interpreter & MIR (12-16 weeks)

#### 5.1 MIR Optimization (Weeks 23-26)
**Rust:** `src/rust/compiler/src/mir/` (optimization passes)
**Simple:** Already exists in `simple/compiler/mir.spl` (basic)

**SSpec Test Plan:**
```spl
# simple/std_lib/test/features/mir_optimization_spec.spl

feature "Constant Folding":
    scenario "Fold arithmetic":
        given:
            val mir = "let x = 2 + 3"
        when:
            val optimized = optimize_mir(mir)
        then:
            optimized == "let x = 5"

feature "Dead Code Elimination":
    scenario "Remove unused variables":
        # Test DCE

feature "Inlining":
    scenario "Inline small functions":
        # Test inlining heuristics
```

**Coverage:** All optimization passes
**Modes:** All 3

#### 5.2 Interpreter Core (Weeks 27-30)
**Rust:** `src/rust/compiler/src/interpreter/` (complex)
**Simple:** Could port to Simple (self-interpreting!)

**SSpec Test Plan:**
```spl
# simple/std_lib/test/features/interpreter_spec.spl

feature "Expression Evaluation":
    scenario "Evaluate arithmetic":
        given:
            val expr = "2 + 3 * 4"
        when:
            val result = interpret(expr)
        then:
            result == 14

feature "Control Flow":
    scenario "If expressions":
        # Test branching

    scenario "Loops":
        # Test while/for

feature "Functions":
    scenario "Call user-defined functions":
        # Test function calls

    scenario "Closures":
        # Test closure capture
```

**Coverage:** All expression types, all control flow
**Modes:** Interpreter only (bootstrapping concern)
**Note:** High complexity, self-referential

---

### Phase 6: Advanced Features (16-20 weeks)

#### 6.1 Async Runtime Integration (Weeks 31-34)
**Rust:** `src/rust/runtime/src/async_runtime/`
**Strategy:** Keep Rust async runtime, add Simple bindings

**SSpec Test Plan:**
```spl
# simple/std_lib/test/features/async_spec.spl

feature "Async Functions":
    scenario "Define async function":
        given:
            val code = "async fn fetch(url): await http.get(url)"
        when:
            val result = parse_and_check(code)
        then:
            result.is_async == true

    scenario "Await expressions":
        # Test await behavior

feature "Async Executor":
    scenario "Schedule tasks":
        # Test task scheduling

    scenario "Handle errors":
        # Test async error propagation
```

**Modes:** All 3 (FFI to Rust tokio)
**FFI Bridge:** Thin wrapper over tokio

#### 6.2 Pattern Matching (Weeks 35-36)
**Rust:** Pattern matching exhaustiveness checker
**Simple:** Exists in compiler

**SSpec Test Plan:**
```spl
# simple/std_lib/test/features/pattern_matching_spec.spl

feature "Exhaustiveness Checking":
    scenario "Detect missing enum variants":
        given:
            val code = """
                match value:
                    case Some(x): x
                # Missing None case
            """
        when:
            val result = check_exhaustiveness(code)
        then:
            result.errors.len() > 0
            result.errors[0].message.contains("non-exhaustive")

    scenario "Detect redundant patterns":
        # Test redundancy check
```

**Coverage:** All pattern types, exhaustiveness rules
**Modes:** All 3

---

## FFI Bridge Strategy

### Keep Rust Wrappers for Downloaded Libraries

**For each external Rust library we use:**

1. **Keep thin Rust FFI wrapper** (src/rust/ffi_bridge/)
2. **Expose as extern functions** to Simple
3. **Write SSpec tests** for the FFI boundary

#### Example: String Interning (lasso)

**Rust FFI Wrapper:**
```rust
// src/rust/ffi_bridge/string_interner.rs
use lasso::{Rodeo, Spur};
use std::sync::Mutex;

static INTERNER: Mutex<Rodeo> = Mutex::new(Rodeo::new());

#[no_mangle]
pub extern "C" fn rt_intern_string(ptr: *const u8, len: usize) -> u64 {
    let bytes = unsafe { std::slice::from_raw_parts(ptr, len) };
    let string = std::str::from_utf8(bytes).unwrap();
    let mut interner = INTERNER.lock().unwrap();
    interner.get_or_intern(string).into_usize() as u64
}

#[no_mangle]
pub extern "C" fn rt_resolve_string(id: u64) -> RuntimeValue {
    let interner = INTERNER.lock().unwrap();
    let spur = Spur::from(id as usize);
    let string = interner.resolve(&spur);
    rt_string_new(string.as_ptr(), string.len() as u64)
}
```

**Simple Usage:**
```spl
# simple/compiler/interner.spl
extern fn rt_intern_string(ptr: i64, len: i64) -> i64
extern fn rt_resolve_string(id: i64) -> text

class StringInterner:
    fn intern(s: text) -> i64:
        rt_intern_string(s.ptr(), s.len())

    fn resolve(id: i64) -> text:
        rt_resolve_string(id)
```

**SSpec Test:**
```spl
# simple/std_lib/test/features/string_interner_spec.spl

feature "String Interning":
    scenario "Intern and resolve":
        given:
            val interner = StringInterner()
        when:
            val id1 = interner.intern("hello")
            val id2 = interner.intern("hello")
            val resolved = interner.resolve(id1)
        then:
            id1 == id2  # Same string gets same ID
            resolved == "hello"
```

**Libraries to Bridge:**
- `lasso` - String interning
- `typed-arena` - Arena allocation
- `memmap2` - Memory-mapped files
- `cranelift-*` - Codegen backend (already bridged)
- `tokio` - Async runtime
- `rayon` - Parallel iteration
- `reqwest` - HTTP client
- `serde` / `serde_json` - Serialization
- etc.

---

## SSpec Test Coverage Targets

### Per-Module Coverage Goals

| Module | Rust Lines | SSpec Tests | Coverage Target |
|--------|-----------|-------------|-----------------|
| SDN parser | 2,000 | 200+ scenarios | 100% branches |
| Dependency tracker | 1,500 | 150+ scenarios | 100% graph paths |
| Diagnostics | 1,000 | 100+ scenarios | 100% message types |
| Package manager | 3,000 | 300+ scenarios | 100% resolver paths |
| LSP server | 5,000 | 200+ scenarios | 100% protocol msgs |
| DAP server | 3,000 | 150+ scenarios | 100% protocol msgs |
| Type inference | 5,000 | 500+ scenarios | 100% inference rules |
| MIR optimizer | 3,000 | 200+ scenarios | 100% passes |
| Interpreter | 10,000 | 500+ scenarios | 95% (complex) |

**Total:** ~1,000-2,000 SSpec test scenarios

---

## Migration Workflow (Per Module)

### Step-by-Step Process

**Week N: Module X**

#### Day 1-2: Analyze & Design Tests
```bash
1. Read Rust source (src/rust/X/)
2. Extract all public functions/types
3. Document behavior in markdown
4. Design SSpec test structure
5. Identify edge cases from Rust tests
```

#### Day 3-5: Write SSpec Tests
```bash
6. Write SSpec feature files
7. Run against Rust (baseline)
8. Ensure 100% pass rate
9. Add missing edge cases
10. Document expected behavior
```

#### Day 6-10: Port to Simple
```bash
11. Create simple/X/ module structure
12. Implement functions one-by-one
13. Run SSpec after each function
14. Fix until tests pass
15. Test in all 3 modes (interpreter, SMF, native)
```

#### Day 11-12: Integration & Cleanup
```bash
16. Integrate with existing Simple code
17. Update imports/dependencies
18. Run full test suite
19. Benchmark performance
20. Document any differences
```

#### Day 13-15: Deprecation
```bash
21. Mark Rust version as deprecated
22. Add migration guide
23. Keep Rust version for 1 release cycle
24. After verification, remove Rust code
```

---

## Three-Mode Testing Strategy

### Test Execution Matrix

**Every SSpec test runs in 3 modes:**

```bash
# Mode 1: Interpreter (fast feedback)
simple test simple/std_lib/test/features/X_spec.spl

# Mode 2: SMF (compiled bytecode)
simple compile simple/std_lib/test/features/X_spec.spl -o /tmp/X_spec.smf
simple /tmp/X_spec.smf

# Mode 3: Native (full AOT)
simple compile simple/std_lib/test/features/X_spec.spl -o /tmp/X_spec --native
/tmp/X_spec
```

**CI Pipeline:**
```yaml
# .github/workflows/test.yml
test_simple_modules:
  strategy:
    matrix:
      mode: [interpreter, smf, native]
      module: [sdn, dependency_tracker, diagnostics, pkg, lsp, dap, type_infer, mir, interpreter]
  steps:
    - name: Test ${{ matrix.module }} in ${{ matrix.mode }} mode
      run: |
        if [ "${{ matrix.mode }}" = "interpreter" ]; then
          simple test simple/std_lib/test/features/${{ matrix.module }}_spec.spl
        elif [ "${{ matrix.mode }}" = "smf" ]; then
          simple compile simple/std_lib/test/features/${{ matrix.module }}_spec.spl -o /tmp/test.smf
          simple /tmp/test.smf
        else
          simple compile simple/std_lib/test/features/${{ matrix.module }}_spec.spl -o /tmp/test --native
          /tmp/test
        fi
```

**Expected Results:**
- Interpreter: Always passes (most features)
- SMF: Passes (compiled mode, some features may differ)
- Native: Passes (full codegen, some advanced features may be FFI)

**If any mode fails:**
1. Document limitation in feature spec
2. Add `mode:` tag to scenario
3. Skip unsupported modes gracefully

```spl
# Example: Feature requires interpreter
feature "Advanced Metaprogramming":
    scenario "Runtime code generation":
        tags: ["interpreter_only"]
        given:
            # This only works in interpreter mode
        # ...
```

---

## Codegen Feature Completion (Prerequisite)

**Before migrating interpreter/MIR, complete native codegen:**

### Missing Codegen Features (From error messages)

1. **Matrix operations (@)**
   - Implement runtime library for matrix multiply
   - Add Cranelift IR generation
   - Test: `A @ B` compiles to native

2. **Pipeline operators (|>, >>, <<, //, ~>)**
   - Implement function dispatch in codegen
   - Add closure support
   - Test: Pipelines work in native mode

3. **Static methods**
   - Generate correct vtable/dispatch
   - Test: `Class.static_method()` works

4. **Async/await**
   - Integrate with tokio via FFI
   - Generate async state machines
   - Test: `async fn` works in native

5. **Context blocks**
   - Implement context tracking in codegen
   - Test: Context statements compile

**Timeline:** 8-12 weeks (before Phase 5)

**Then:** Simple compiler can compile itself natively!

---

## Success Criteria (Per Module)

### Migration Acceptance Checklist

**Module X is ready to replace Rust when:**

- [ ] 100% SSpec test coverage of Rust functionality
- [ ] All tests pass in interpreter mode
- [ ] All tests pass in SMF mode
- [ ] All tests pass in native mode (or documented limitations)
- [ ] Performance within 2x of Rust (in native mode)
- [ ] Memory usage within 1.5x of Rust
- [ ] No regressions in dependent modules
- [ ] Documentation complete (API docs, migration guide)
- [ ] Code review approved
- [ ] 1 release cycle in production (beta)

**Final Removal of Rust Code:**
- [ ] 2 releases (8 weeks) with Simple version stable
- [ ] No bug reports related to migration
- [ ] Performance benchmarks stable
- [ ] Deprecation warnings in Rust code for 1 release

---

## Risk Mitigation

### High-Risk Modules

**Interpreter (self-referential):**
- Risk: Interpreter interpreting itself = performance cliff
- Mitigation: Keep Rust interpreter as fallback
- Test: Bootstrap with Simple interpreter, measure slowdown
- Acceptance: 5x slowdown acceptable, >10x requires optimization

**Type Inference (complex algorithms):**
- Risk: Bugs cause silent incorrect compilation
- Mitigation: Extensive SSpec tests, cross-check with Rust
- Test: 500+ type inference scenarios
- Acceptance: Zero type soundness bugs

**MIR Optimizer (correctness-critical):**
- Risk: Optimization bugs cause wrong code generation
- Mitigation: Test optimized vs unoptimized equivalence
- Test: Compare outputs, fuzz testing
- Acceptance: Zero correctness bugs, performance within 1.5x

### Rollback Plan

**If migration fails:**

1. **Keep Rust version** (don't delete!)
2. **Feature flag:** `SIMPLE_USE_RUST_X=1`
3. **Gradual rollout:** 10% → 50% → 100% traffic
4. **Monitor metrics:** Performance, crashes, correctness
5. **Quick rollback:** Flip flag back to Rust

---

## Timeline Summary

### v0.4.0 (6 months)

| Phase | Weeks | Modules | SSpec Tests |
|-------|-------|---------|-------------|
| **Phase 1** | 1-6 | SDN, deps, diagnostics | 450+ scenarios |
| **Phase 2** | 7-13 | Package mgr, build | 500+ scenarios |
| **Phase 3** | 14-22 | LSP, DAP, formatter | 550+ scenarios |
| **Phase 4** | 23-30 | Type system, MIR | 900+ scenarios |
| **Phase 5** | 31-36 | Interpreter, async | 650+ scenarios |
| **Total** | 36 weeks | 15-20 modules | 3,000+ scenarios |

**Parallel Work:**
- Codegen completion: Weeks 1-12 (parallel with Phase 1-2)
- Documentation: Continuous
- Performance tuning: Weeks 30-36

---

## Deliverables

### Code Artifacts

1. **SSpec Test Suite** - 3,000+ scenarios
   - `simple/std_lib/test/features/X_spec.spl` for each module
   - 100% coverage of ported functionality
   - Runs in all 3 modes

2. **Simple Implementations** - 20+ modules
   - Pure Simple code (no unsafe)
   - All in `simple/` or `src/app/`
   - Documented APIs

3. **FFI Bridge Layer** - Thin wrappers
   - `src/rust/ffi_bridge/` - ~5,000 lines
   - Wrappers for lasso, arena, mmap, tokio, etc.
   - Minimal unsafe code

4. **Migration Guides** - Documentation
   - Per-module migration notes
   - API compatibility matrix
   - Performance comparison

### Process Artifacts

1. **Test Coverage Reports** - Per module
2. **Performance Benchmarks** - Rust vs Simple
3. **Memory Profiles** - Allocation analysis
4. **Rollback Procedures** - If migration fails

---

## Post-Migration Optimization (v0.5.0+)

**After migration complete, optimize:**

1. **JIT Compilation** - Hot loop optimization
2. **Inlining** - Reduce FFI overhead
3. **Specialization** - Monomorphize generics
4. **Cache Optimization** - Better memory layout
5. **Parallel Execution** - Use rayon FFI

**Expected Results:**
- 2-5x speedup over interpreted
- Within 1.2x of Rust performance
- 80%+ native execution (20% interpreter fallback)

---

## Conclusion

### Strategy Summary

1. **Write SSpec tests FIRST** - 100% coverage before porting
2. **Port incrementally** - Module by module, verify each
3. **Test in 3 modes** - Interpreter, SMF, native
4. **Keep FFI bridges** - Don't rewrite downloaded libraries
5. **Gradual rollout** - Feature flags, monitoring, rollback
6. **Performance validation** - Within 2x of Rust
7. **Long verification** - 2 release cycles before deletion

**Success Metric:** 90%+ of codebase in Simple, 100% test pass rate, <2x performance overhead

**Timeline:** 6-9 months for full migration, safe and verified

**Risk:** Low - incremental, test-first, with rollback

🎯 **Goal:** Self-hosted Simple compiler that's as fast and reliable as Rust! 🚀
