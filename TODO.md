# TODO

This file tracks active development priorities. For detailed implementation plans, see `doc/plans/`.

## new struct refactoring
lets make and migrate existing spl code to here. simple langauge package and lib development dir
so, make spl lib development itself easier.

simple/bin/ < place binary tools and make it .gitignore
simple/std_lib/ < spl library files.
simple/std_lib/src/
simple/std_lib/test/
simple/doc/ < link to doc/

## Active Development

### 1. Contract Blocks (#400) - LLM-Friendly Feature
**Status:** 25% Complete (Parser Phase 1)  
**Priority:** High  
**Plan:** `doc/plans/llm_friendly.md`

**Completed:**
- ✅ Keywords added to lexer (requires, ensures, invariant, old)
- ✅ AST nodes (ContractBlock, InvariantBlock, ContractClause)
- ✅ Parsing logic (parse_contract_block, parse_invariant_block)

**Next Steps:**
- Wire parsing into function/class definitions
- Add parsing tests
- Implement type checking for contracts
- Generate runtime assertions

**See:** `doc/feature.md` #400-410 for all LLM-friendly features

---

### 2. JJ Version Control Integration (#303)
**Status:** 67% Complete (8/12 tasks)  
**Priority:** Medium  
**Plan:** `doc/plans/27_jj_integration.md`

**Completed:**
- ✅ Core state management (JjStateManager)
- ✅ Event system (BuildEvent types)
- ✅ CLI integration (--snapshot flag)
- ✅ Unit tests (2 passing)
- ✅ Integration tests (15 passing)

**Remaining:**
- Test success tracking (blocked on test framework)
- System tests
- Documentation

---

### 3. BDD Spec Framework (#300)
**Status:** 70% of Sprint 1, 28% overall  
**Priority:** High (Testing Infrastructure)  
**Plan:** `doc/plans/28_bdd_spec.md`

**Sprint 1 Complete (10/12):**
- ✅ DSL, Registry, Runtime, Matchers all implemented

**Sprint 1 Remaining:**
- Unit tests for DSL and matchers
- Test registry functionality

**Sprint 2 Planned:**
- Runner CLI, executor, formatters

---

### 4. Simple Doctest (#301)
**Status:** 90% effective completion  
**Priority:** High (Testing Infrastructure)  
**Plan:** `doc/plans/29_doctest.md`

**Sprint 1 Complete:**
- ✅ Parser, Matcher, Runner (40+ unit tests)

**Sprint 2 Complete (Effective):**
- ✅ Discovery framework
- ✅ FFI bridge (7 functions, 7 tests)
- ✅ Markdown extraction
- ✅ Glob pattern matching
- ✅ Integration tests (19 test cases)

**Blocked:**
- CLI integration (needs infrastructure)
- Interpreter execution (needs Simple runtime)

---

## Planned Development

### High Priority
1. **LLM-Friendly Features (#400-410)** - Contract blocks in progress
2. **Test Framework Completion** - BDD + Doctest finishing touches
3. **Language Server (LSP)** - Editor support (Plan: `doc/plans/30_pending_features.md`)

### Medium Priority
4. **Test CLI Integration (#302)** - Unified `simple test` command
5. **Convention Documentation** - Update language spec with conventions
6. **TUI Framework** - Terminal UI library
7. **Package Registry** - Central repository (crates.io-style)

### Low Priority
8. **Web Framework** - Ruby on Rails-style framework
9. **GUI Framework** - Native or Immediate Mode GUI
10. **Debugger (DAP)** - Debug Adapter Protocol support

**See:** `doc/plans/30_pending_features.md` for full details

---

## Completed

All completed features are tracked in `doc/feature.md` with ✅ status.

Major completed systems:
- ✅ Parser, Lexer, AST
- ✅ HIR, MIR, Codegen (Cranelift + Interpreter)
- ✅ Runtime value system (9 modules, 50+ FFI functions)
- ✅ SMF binary format and loader
- ✅ Package manager (UV-style)
- ✅ Module system with imports/exports
- ✅ Embedded support (ARM Cortex-M, RISC-V)
- ✅ Effect system (@async, effect checking)
- ✅ Primitive API linting
- ✅ Doctest Sprint 1 & 2
- ✅ BDD Spec Sprint 1

**See:** `doc/feature.md` for complete status

---

## Ignored/Deferred

**Ignored Tests:**
- Generator JIT codegen (needs block layout hookup)
- Unit conversion methods (not yet implemented)
- Embedded panic customization (doctest placeholder)

**Deferred Features:**
- GPU backends (WGPU, Metal)
- 32-bit architecture support (needs LLVM backend)
- Test state storage (JJ integration - blocked on test framework)

---

## Quick Reference

**Documentation:**
- `doc/feature.md` - Complete feature list with status
- `doc/plans/` - Detailed implementation plans (30+ files)
- `doc/spec/` - Language specifications
- `doc/status/` - Feature implementation status (79+ files)

**Commands:**
- `make test` - Run all tests
- `make coverage` - Generate coverage report
- `make lint` - Run linter
- `make fmt` - Format code
- `make check` - Pre-commit checks (fmt + lint + test)

**Current Focus:** Contract blocks implementation (LLM-friendly feature #400)

