# TODO

## In Progress

### JJ Version Control Integration
**Status:** Core Implementation Complete + Event System Added
**Goal:** Auto-snapshot successful builds and test runs to JJ
**Implementation:** 
- `src/driver/src/jj_state.rs` - State management with JJ CLI
- `src/driver/src/jj/` - Event system and state storage

**Completed:**
1. ✅ JjStateManager - Core state management with JJ CLI integration
2. ✅ BuildMetadata - Track build success, duration, artifacts, mode
3. ✅ TestMetadata - Track test results, duration, pass/fail/ignored counts
4. ✅ Automatic snapshot creation on build/test success
5. ✅ Last working state retrieval
6. ✅ Unit tests for display methods (2 tests passing)
7. ✅ Integration tests - 15/15 tests passing (`tests/jj_state_tests.rs`)
   - Build snapshots (8 tests)
   - Test snapshots (4 tests)
   - Edge cases and idempotency (3 tests)
8. ✅ **NEW: JJ Connection Infrastructure (12 tests passing)**
   - `jj/event.rs` - BuildEvent and BuildState types
   - `jj/store.rs` - StateStore for persistent build history
   - `jj/jj.rs` - JJConnector for JJ CLI integration
   - `jj/message.rs` - MessageFormatter for user-facing messages

**Remaining:**
1. ⏳ CLI integration (`--snapshot` flag for build/test commands)
2. ⏳ Wire compilation/test success into BuildEvent capture
3. ⏳ System tests for end-to-end snapshot workflow
4. ⏳ Documentation (usage guide, examples)
5. 🔒 Test State Storage (DEFERRED - pending test framework setup)

---

## In Progress

### BDD Spec Framework (RSpec-style for Simple)
**Status:** Sprint 1 - Core DSL & Registry (Phase 1-2)
**Goal:** Ruby/RSpec-style BDD test framework written in Simple
**Spec:** `doc/bdd_spec.md`

**Completed:**
1. ✅ Directory structure (`lib/std/spec/`)
2. ✅ Core DSL (`dsl.spl`) - describe, context, it, let, hooks
3. ✅ Registry (`registry.spl`) - ExampleGroup, Example, Hook storage
4. ✅ Runtime (`runtime.spl`) - Configuration and state management
5. ✅ Expectations (`expect.spl`) - expect/to/not_to, expect_raises
6. ✅ Matcher Protocol (`matchers.spl`) - Base Matcher trait
7. ✅ Core Matchers (`matchers/core.spl`) - eq, be, be_nil
8. ✅ Comparison Matchers (`matchers/comparison.spl`) - gt, lt, gte, lte
9. ✅ Collection Matchers (`matchers/collection.spl`) - include, be_empty
10. ✅ Error Matchers (`matchers/error.spl`) - raise_error

**Next Steps (Sprint 1 Remaining):**
1. ⏳ Write unit tests for DSL and matchers
2. ⏳ Test registry functionality

**Sprint 2 (Planned):**
- Runner implementation (`runner/cli.spl`, `runner/executor.spl`)
- Formatters (progress, doc, json)
- Integration tests

**Sprint 3 (Planned):**
- Coverage infrastructure in compiler
- symbols.json emission
- Public API coverage calculation

**Sprint 4 (Planned):**
- Test environment setup (`test/` folder structure)
- Migration guide
- Documentation

---

## In Progress

### Simple Doctest (sdoctest) Framework
**Status:** Phase 1 - Core Parser and Runner
**Goal:** Python doctest-style interactive tests embedded in docstrings and docs
**Spec:** `doc/spec/sdoctest.md`

**Features:**
- `>>>` prompt syntax for executable examples
- Extract from docstrings (`///`), Markdown (` ```simple-doctest `), and `.sdt` files
- Integrated with BDD spec framework runner
- Coverage contribution to public function touch
- REPL recording mode (`--record`)
- Wildcard matching for non-deterministic output
- Setup/teardown blocks per docstring
- Tag-based filtering

**Sprint 1: Core Parser and Runner**
1. ✅ Create `lib/std/doctest/` module structure
2. ✅ Implement parser (`parser.spl`):
   - Extract `>>>` examples from strings
   - Parse expected output
   - Parse exception expectations (`Error: Type`)
   - Extract docstrings from `.spl` files
   - Parse setup/teardown blocks
3. ✅ Implement matcher (`matcher.spl`):
   - Exact string matching with normalization
   - Wildcard matching (`.` and `*`)
   - Exception matching
4. ✅ Implement runner (`runner.spl`):
   - Execute code in isolated interpreter (placeholder)
   - Capture stdout/stderr
   - Match output vs expected
   - Setup/teardown execution
5. ✅ Create stub modules:
   - `discovery.spl` - File discovery framework
   - `reporter.spl` - Result formatting
   - `integration.spl` - Spec runner integration
6. ✅ Write 40+ unit tests for parser, matcher, and runner
7. ⏳ Wire interpreter integration (pending Simple REPL/interpreter API)
8. ⏳ Run tests and verify basic functionality

**Sprint 2: Discovery and Integration (Planned)**
- Discovery from `.spl`, `.md`, `.sdt` files
- Hook into `spec.runner` for unified test execution
- CLI: `simple test --doctest`
- Integration tests

**Sprint 3: Advanced Features (Planned)**
- Wildcard matching (`.` and `*`)
- Setup/teardown isolation
- Tag filtering (`@doctest(tag: ...)`)
- REPL recording mode

**Sprint 4: Coverage and Polish (Planned)**
- Coverage integration (public function touch)
- Configuration (`simple.toml`)
- Migration guide
- Example library

---

## Pending

### LLM-Friendly Test Infrastructure
- Minimal context interface
- System test public class/struct touch coverage
- System test mock usage limits
- Integration test public function touch coverage
- Config-driven docs instructions
- Task runner for coverage, docs, lint
### update lanagauage spec << convension over config
### gui support
#### ruby rails spring like framework
#### tui


## Completed

### Embedded Support (src/embedded/)
**Startup code:**
- ARM Cortex-M (M0, M3, M4, M7) - vector tables, NVIC, SysTick
- RISC-V (RV32, RV64) - CSR, PLIC, CLINT
- Linker scripts for both architectures

**Teardown module:**
- Settlement SSMF parsing for embedded targets
- Intel HEX and S-Record output formats
- Target configs: STM32F103, STM32F4, nRF52832, ESP32-C3, RISC-V QEMU

**Variants module:**
- Feature flags: `no-float`, `no-alloc`, `no-thread`, `no-gc`
- Presets: `minimal`, `embedded-tiny`, `embedded-small`
- Fixed-point math (Q16.16) for float-less targets
- Static containers for alloc-less targets
- Cooperative scheduler for thread-less targets
- Memory pools and arenas for GC-less targets

---

## Ignored Tests (features not yet implemented)

### Generator JIT codegen
- **Test:** `jit_generator_dispatcher_yields_and_restores`
- **File:** `src/compiler/tests/generator_codegen.rs:14`
- **Reason:** Requires stable block layout hookup; dispatcher path covered in runtime test

### Unit conversion methods
- **Test:** `interpreter_unit_family_to_base`
- **File:** `src/driver/tests/interpreter_types.rs:473`
- **Reason:** Unit conversion methods (`.to_m()`) not yet implemented

### Embedded panic customization
- **Test:** `doc test src/embedded/src/lib.rs - (line 22)` (ignored)
- **File:** `src/embedded/src/lib.rs`
- **Reason:** Doc-test kept ignored for no_std placeholder entry macro
- **Status:** Postponed; keep ignored until a host-friendly doctest harness exists

---  
## add convention over config to rule on language spec
## Postponed

### GPU backends
- WGPU/WebGPU backend integration
- Metal backend (Apple)

### 32-bit architecture support
**Status:** Deferred - requires LLVM backend
**Reason:** Cranelift does not support 32-bit (ARM32 was removed)
