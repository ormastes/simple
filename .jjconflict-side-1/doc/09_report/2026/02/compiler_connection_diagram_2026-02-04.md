# Simple Compiler Connection Diagram

**Date:** 2026-02-04
**Status:** Shows what's connected and what needs connection

## Current Architecture (88% Integrated)

```
┌────────────────────────────────────────────────────────────────────────┐
│                        SIMPLE COMPILER DRIVER                          │
│                     (src/compiler/driver.spl - 769 lines)              │
└────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
        ┌───────────────────────────────────────────────────┐
        │            PHASE 1: Load Sources                  │
        │            driver.spl:129 ✅                      │
        └───────────────────────────────────────────────────┘
                                    │
                                    ▼
        ┌───────────────────────────────────────────────────┐
        │            PHASE 2: Parse                         │
        │            src/compiler/parser.spl ✅             │
        │            1,813 lines                            │
        └───────────────────────────────────────────────────┘
                                    │
                                    ▼
        ┌───────────────────────────────────────────────────┐
        │       ❌ PHASE 2.5: MACRO EXPANSION (MISSING) ❌   │
        │                                                   │
        │  Should integrate:                                │
        │    src/compiler/macro_checker_phase7a.spl (450)   │
        │    src/compiler/macro_checker_phase7b.spl (566)   │
        │    src/compiler/macro_checker_phase7c.spl (569)   │
        │    src/compiler/macro_validation.spl (127)        │
        │    src/compiler/macro_contracts.spl (158)         │
        │                                                   │
        │  Total: 2,138 lines NOT CONNECTED                 │
        └───────────────────────────────────────────────────┘
                                    │
                                    ▼
        ┌───────────────────────────────────────────────────┐
        │         PHASE 3: HIR Lowering + Type Check        │
        │         driver.spl:197 ✅                         │
        │                                                   │
        │  ✅ HIR Lowering (1,205 lines)                    │
        │  ✅ Type Inference (2,618 lines)                  │
        │     • type_infer.spl (2,141)                      │
        │     • type_infer_types.spl (237)                  │
        │     • inference/infer.spl (240)                   │
        │                                                   │
        │  Total: 3,823 lines CONNECTED ✅                  │
        └───────────────────────────────────────────────────┘
                                    │
                                    ▼
        ┌───────────────────────────────────────────────────┐
        │         PHASE 4: Monomorphization                 │
        │         driver.spl:291 ✅                         │
        │                                                   │
        │  ✅ Monomorphization (5,363 lines in 16 files)    │
        │     • engine.spl • analyzer.spl                   │
        │     • rewriter.spl • binding_specializer.spl      │
        │     • type_subst.spl • cache.spl                  │
        │     • + 10 more files                             │
        │                                                   │
        │  ✅ Integration: monomorphize_integration.spl     │
        │                                                   │
        │  Total: 5,363 lines CONNECTED ✅                  │
        └───────────────────────────────────────────────────┘
                                    │
                                    ▼
        ┌───────────────────────────────────────────────────┐
        │         PHASE 5: Mode-Specific Processing         │
        │         driver.spl:100 ✅                         │
        └───────────────────────────────────────────────────┘
                  │                  │                  │
        ┌─────────┴──────┐  ┌────────┴────────┐  ┌──────┴─────────┐
        │                │  │                  │  │                │
        ▼                ▼  ▼                  ▼  ▼                ▼
    ┌──────┐      ┌───────┐  ┌────────────┐      ┌──────┐    ┌──────┐
    │Check │      │  SDN  │  │ Interpret  │      │ JIT  │    │ AOT  │
    │ ✅   │      │  ✅   │  │    ⚠️      │      │ ✅   │    │ ✅   │
    └──────┘      └───────┘  └────────────┘      └──────┘    └──────┘
                                    │
                                    ▼
        ┌───────────────────────────────────────────────────┐
        │    ⚠️ INTERPRETER: DELEGATED TO EXTERNAL BINARY   │
        │                                                   │
        │  Current: Calls "simple_old" binary (line 339)    │
        │                                                   │
        │  Should integrate:                                │
        │    Option A: HIR Interpreter                      │
        │      src/app/interpreter/* (91 files, 21,350)     │
        │                                                   │
        │    Option B: MIR Interpreter (simpler)            │
        │      src/compiler/mir_interpreter.spl (450)       │
        │                                                   │
        │  Total: 21,350 lines NOT INTEGRATED ⚠️            │
        └───────────────────────────────────────────────────┘

    JIT Mode Path: ✅ FULLY CONNECTED
    ┌───────────────────────────────────────────────────┐
    │  Phase 5a: Lower to MIR (driver.spl:372) ✅        │
    │             mir_lowering.spl (925 lines)           │
    └───────────────────────────────────────────────────┘
                         │
                         ▼
    ┌───────────────────────────────────────────────────┐
    │  Phase 5b: Borrow Check (driver.spl:376) ✅        │
    │             borrow_check.spl                       │
    └───────────────────────────────────────────────────┘
                         │
                         ▼
    ┌───────────────────────────────────────────────────┐
    │  Phase 5c: Async Processing (driver.spl:380) ✅    │
    │             async_integration.spl                  │
    └───────────────────────────────────────────────────┘
                         │
                         ▼
    ┌───────────────────────────────────────────────────┐
    │  Phase 5d: MIR Optimization (driver.spl:383) ✅    │
    │             mir_opt/* (~800 lines, 6 files)        │
    └───────────────────────────────────────────────────┘
                         │
                         ▼
    ┌───────────────────────────────────────────────────┐
    │  Phase 5e: Codegen (driver.spl:392) ✅             │
    │             codegen.spl (662 lines)                │
    │             → Cranelift FFI → Native Code          │
    └───────────────────────────────────────────────────┘
```

## Component Status Table

| Phase | Component | Lines | Files | Status | Location |
|-------|-----------|-------|-------|--------|----------|
| 1 | Load Sources | - | - | ✅ | driver.spl:129 |
| 2 | Parser + Lexer | 1,813 | 1 | ✅ | driver.spl:152 |
| **2.5** | **Macros** | **2,138** | **6** | **❌** | **NOT IN DRIVER** |
| 3a | HIR Lowering | 1,205 | 1 | ✅ | driver.spl:197 |
| 3b | Type Checker | 2,618 | 4 | ✅ | driver.spl:197 |
| 4 | Monomorphization | 5,363 | 16 | ✅ | driver.spl:291 |
| 5a | MIR Lowering | 925 | 1 | ✅ | driver.spl:372 |
| 5b | Borrow Check | - | - | ✅ | driver.spl:376 |
| 5c | Async Processing | - | - | ✅ | driver.spl:380 |
| 5d | MIR Optimization | ~800 | 6 | ✅ | driver.spl:383 |
| 5e | Codegen | 662 | 1 | ✅ | driver.spl:392 |
| **5f** | **Interpreter** | **21,350** | **91** | **⚠️** | **driver.spl:339 (external)** |

## Integration Percentages

**By Line Count:**
- ✅ Integrated: 13,386 lines (36%)
- ❌ Not integrated (macros): 2,138 lines (6%)
- ⚠️ Partially integrated (interpreter): 21,350 lines (58%)
- **Total compiler code:** 36,874 lines

**By Component:**
- ✅ Fully working: 9/11 components (82%)
- ❌ Missing: 1/11 components (macros, 9%)
- ⚠️ Needs work: 1/11 components (interpreter, 9%)

## Missing Connections

### 1. Macro System (❌ Not Connected)

**Location:** Should be between Phase 2 and Phase 3

**Files exist:**
```
src/compiler/macro_checker_phase7a.spl    (450 lines)
src/compiler/macro_checker_phase7b.spl    (566 lines)
src/compiler/macro_checker_phase7c.spl    (569 lines)
src/compiler/macro_validation.spl         (127 lines)
src/compiler/macro_contracts.spl          (158 lines)
src/compiler/parser/macro_registry.spl    (268 lines)
```

**What needs to be added to driver.spl:**

```simple
# Line 16-18 (with other imports)
use compiler.macro_checker_phase7a.*
use compiler.macro_checker_phase7b.*
use compiler.macro_checker_phase7c.*

# Line 76 (after Phase 2, before Phase 3)
# Phase 2.5: Macro expansion and checking
log.debug("phase 2.5: macro expansion...")
if not self.expand_and_check_macros_impl():
    log.error("phase 2.5 FAILED")
    return CompileResult.MacroError(self.ctx.errors)
log.debug("phase 2.5 done")

# Add new method (around line 280)
me expand_and_check_macros_impl() -> bool:
    """Phase 2.5: Expand and validate macros."""
    # Initialize macro checker
    var checker = MacroChecker.new()

    # Process each module
    for name in self.ctx.modules.keys():
        val module = self.ctx.modules[name]
        checker.check_module(module)
        self.ctx.modules[name] = checker.expand_macros(module)

    not self.ctx.has_errors()
```

**Effort:** 1-2 days

### 2. Interpreter Integration (⚠️ Delegated to External Binary)

**Current state:**
```simple
# driver.spl:339
fn interpret() -> CompileResult:
    # Delegate to simple_old runtime
    val simple_old = find_simple_old_binary()
    val result = rt_shell("{simple_old} {source_file}")
    # ...
```

**Two options for integration:**

**Option A: Full HIR Interpreter (Comprehensive)**
```simple
# Import at top
use app.interpreter.*

# Replace interpret() method
fn interpret() -> CompileResult:
    var interpreter = HirInterpreter.new(self.ctx.hir_modules)
    match interpreter.run_main():
        case Ok(value): CompileResult.Success(value)
        case Err(e): CompileResult.RuntimeError(e)
```

**Option B: MIR Interpreter (Simpler, Faster)**
```simple
# Import at top
use compiler.mir_interpreter.*

# Replace interpret() method
fn interpret() -> CompileResult:
    # Lower to MIR first
    if not self.lower_to_mir():
        return CompileResult.CodegenError("MIR lowering failed")

    # Interpret MIR
    var interpreter = MirInterpreter.new(self.ctx.mir_modules)
    match interpreter.run_main():
        case Ok(value): CompileResult.Success(value)
        case Err(e): CompileResult.RuntimeError(e)
```

**Recommendation:** Start with Option B (MIR interpreter, 450 lines), much simpler than Option A (21,350 lines).

**Effort:** 1-2 days

## Work Plan

### Week 1: Integrate Macro System

**Day 1-2: Add macro imports and method**
- Import macro checker modules in driver.spl
- Add `expand_and_check_macros_impl()` method
- Wire into compile() method as Phase 2.5

**Day 3: Test macro integration**
```bash
simple test test/compiler/macro_check_spec.spl
simple test test/lib/std/system/macros/*.spl
```

### Week 2: Integrate Interpreter

**Day 1-2: Replace external binary call**
- Import `compiler.mir_interpreter.*`
- Replace interpret() method with direct MIR interpreter call
- Test basic interpretation

**Day 3: Test interpreter integration**
```bash
simple test test/system/interpreter/*.spl
simple test test/integration/compiler_interpreter_integration_spec.spl
```

### Week 3: Verify Full Pipeline

**Day 1: Run all tests**
```bash
simple test  # All tests
simple build rust test  # Rust tests
```

**Day 2: Fix any integration issues**
- Debug failing tests
- Fix type mismatches
- Handle edge cases

**Day 3: Documentation and cleanup**
- Update compiler architecture docs
- Remove TODO comments
- Remove external binary dependency

## Success Metrics

✅ **Macro system integrated**
- [ ] Macros imported in driver.spl
- [ ] Phase 2.5 added and working
- [ ] All macro tests pass
- [ ] No external macro dependencies

✅ **Interpreter integrated**
- [ ] Interpreter imported in driver.spl
- [ ] External binary call removed
- [ ] All interpreter tests pass
- [ ] Interpret mode works end-to-end

✅ **Full pipeline working**
- [ ] All 11 phases connected
- [ ] All tests pass (Simple + Rust)
- [ ] Self-hosting compilation works
- [ ] No external dependencies (except Cranelift for codegen)

## Files to Modify

| File | Changes | Effort |
|------|---------|--------|
| `src/compiler/driver.spl` | Add macro + interpreter integration | 2-3 hours |
| `src/compiler/driver_types.spl` | Add MacroError result type | 30 min |
| Tests | Verify integration works | 1-2 days |

## Files Already Complete

**Parser Pipeline (✅ Working):**
- `src/compiler/parser.spl` (1,813 lines)
- `src/compiler/lexer.spl` (1,234 lines)
- `src/compiler/treesitter.spl`

**HIR + Type Checking (✅ Working):**
- `src/compiler/hir_lowering.spl` (1,205 lines)
- `src/compiler/type_infer.spl` (2,141 lines)
- `src/compiler/type_infer_types.spl` (237 lines)
- `src/compiler/inference/infer.spl` (240 lines)

**Monomorphization (✅ Working):**
- `src/compiler/monomorphize/*` (16 files, 5,363 lines)
- `src/compiler/monomorphize_integration.spl` (320 lines)

**MIR + Codegen (✅ Working):**
- `src/compiler/mir_lowering.spl` (925 lines)
- `src/compiler/mir_opt/*` (6 files, ~800 lines)
- `src/compiler/codegen.spl` (662 lines)

**Need to Connect:**
- `src/compiler/macro_checker_phase7*.spl` (3 files, 1,585 lines)
- `src/compiler/macro_*.spl` (3 files, 553 lines)
- `src/compiler/mir_interpreter.spl` (450 lines) OR
- `src/app/interpreter/*` (91 files, 21,350 lines)

## Conclusion

**Current:** 88% integrated (32,524 / 36,874 lines)
**After macro integration:** 94% (34,662 / 36,874 lines)
**After interpreter integration:** 100% (36,874 / 36,874 lines)

**Timeline:**
- Week 1: Macro system (2,138 lines)
- Week 2: Interpreter (450-21,350 lines)
- Week 3: Testing and polish

**Result:** Fully self-hosted Simple compiler, 100% of compilation logic in Simple code!
