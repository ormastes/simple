# Simple Language Compiler - File & Class Structure Analysis

**Date:** 2026-03-02
**Status:** Comprehensive Inventory & Refactoring Guide
**Scope:** Full codebase (5,644 .spl files, 1,107,838 lines)

---

## Executive Summary

### Codebase Statistics (2026-03-02)

| Metric | Value | Notes |
|--------|-------|-------|
| **Total .spl Files** | 5,644 | src/ (3,708) + test/ (1,772) + examples/ (130) + doc/ (34) |
| **Total .spl Lines** | 1,107,838 | src/ (779,948) + test/ (327,890) |
| **Core Lines (src/)** | 779,948 | All Simple source code |
| **Rust Lines** | 482,983 | Rust seed bootstrap compiler |
| **C Lines** | 28,582 | C bootstrap (16,208) + runtime (12,374) |
| **Test Lines (test/)** | 327,890 | 1,772 test files |
| **Directories** | 8,988 | Full project structure |
| **Documentation** | 3,462 | Markdown files in doc/ |

### Distribution by Directory

| Directory | Files | Lines | Purpose |
|-----------|-------|-------|---------|
| `src/lib/` | 1,546 | 317,086 | Standard library (also symlinked as `src/std/`) |
| `src/compiler/` | 918 | 207,912 | Self-hosted compiler (17 numbered layers) |
| `src/compiler_rust/lib/` | 712 | 174,178 | Stdlib copy for Rust bootstrap |
| `src/app/` | 479 | 75,423 | Applications & tools (CLI, MCP, LSP, test runner) |
| `src/i18n/` | 29 | 4,801 | Internationalization |
| `src/compiler_cpp/` | 15 (C) | 16,208 | Generated C bootstrap source |
| `src/runtime/` | 48 (C) | 12,374 | C runtime (linked by generated C++) |
| `src/compiler_rust/` | 1,800 (Rust) | 482,983 | Rust seed bootstrap compiler |

**Note:** `src/std/` is a symlink to `src/lib/`. `src/compiler/mdsoc/` is a symlink to `src/compiler/85.mdsoc/`.

### Key Architectural Highlights

1. **100% Pure Simple** - Self-hosted compiler written entirely in Simple
2. **Self-Hosting** - Stage 3 complete: Simple compiles itself (fixed-point reached)
3. **Multi-Backend** - LLVM, Cranelift, Native (x86-64, AArch64, RISC-V), WASM, C, Interpreter
4. **Comprehensive Stdlib** - 1,546 files covering networking, crypto, data structures, MCP, testing
5. **Numbered Compiler Layers** - 17 layers (00.common through 99.loader) with clear dependencies
6. **Rust Seed Bootstrap** - Rust compiler bootstraps the pure Simple compiler, then self-hosted
7. **12 disabled library directories deleted** - browser, coverage, doctest, electron, godot, graphics, ml, parser, ui, units, unreal, web removed from `compiler_rust/lib/std/`

---

## 1. Complete Directory Tree

### 1.1 Compiler (`src/compiler/` - 918 files, 207,912 lines)

**Purpose:** Self-hosted compiler written entirely in Simple. Organized into 17 numbered layers with clear dependency ordering. The number prefix (NN.) is stripped for imports.

#### Compiler Layer Architecture

| Layer | Files | Lines | Purpose |
|-------|-------|-------|---------|
| `00.common/` | 40 | 6,933 | Error types, config, effects, visibility, diagnostics |
| `10.frontend/` | 90 | 31,245 | Lexer, parser, AST, tree-sitter, desugar |
| `15.blocks/` | 24 | 4,329 | Block definition system (custom blocks, testing blocks) |
| `20.hir/` | 17 | 4,965 | HIR types, definitions, lowering, inference |
| `25.traits/` | 8 | 1,932 | Trait def, impl, solver, coherence, validation |
| `30.types/` | 53 | 18,901 | Type inference, type system, dimension constraints |
| `35.semantics/` | 26 | 6,843 | Semantic analysis, lint, narrowing, safety checker |
| `40.mono/` | 20 | 6,340 | Monomorphization, instantiation |
| `50.mir/` | 15 | 4,521 | MIR types, data, instructions, lowering |
| `55.borrow/` | 8 | 2,841 | Borrow checking, GC analysis |
| `60.mir_opt/` | 21 | 7,208 | MIR optimization passes (vectorize, inline, const-fold, string_builder) |
| `70.backend/` | 186 | 50,500 | Backends (LLVM, C, Cranelift, WASM, Native), linker, codegen |
| `80.driver/` | 81 | 17,869 | Driver, pipeline, project, build mode, incremental |
| `85.mdsoc/` | 118 | 4,655 | MDSOC (virtual capsules, feature, transform, weaving) |
| `90.tools/` | 169 | 30,068 | API surface, coverage, query, symbol analyzer, AOP, lint |
| `95.interp/` | 10 | 1,801 | Interpreter, MIR interpreter, execution |
| `99.loader/` | 20 | 6,405 | Module resolver, loader, JIT instantiator |
| `test*/` | 10 | 523 | Compiler test fixtures |
| **Total** | **918** | **207,912** | |

**Symlink:** `src/compiler/mdsoc/` -> `85.mdsoc/` (convenience alias)

**Legacy empty dirs:** `backend/`, `common/`, `driver/`, `frontend/`, `interp/`, `linker/`, `loader/`, `mir/` (0 files each, remnants of pre-numbered layout)

#### Deleted Files (since 2026-02-16)
- `00.common/registry/mod.spl` - Registry module removed
- `core/aop_debug_log.spl` - AOP debug log removed
- `core/backend_types.spl` - Backend types consolidated
- `core/interpreter/jit.spl` - JIT moved to numbered layer
- `core/lexer.spl` - Lexer moved to numbered layer
- `linker/smf_reader.spl` - SMF reader removed
- `99.loader/mod.spl` - Loader module entry point removed

#### New Files (since 2026-02-16)
- `60.mir_opt/mir_opt/string_builder_opt.spl` - String builder optimization pass

---

### 1.2 Standard Library (`src/lib/` - 1,546 files, 317,086 lines)

**Purpose:** Comprehensive standard library covering all common needs. Accessible as `use std.X` or `use lib.X` (the module resolver rewrites `std` -> `lib` internally). `src/std/` is a symlink to `src/lib/`.

#### Library Structure

| Directory | Files | Lines | Purpose |
|-----------|-------|-------|---------|
| `common/` | 676 | 145,108 | Pure functions, no mutation (text, math, json, crypto, encoding) |
| `nogc_sync_mut/` | 592 | 124,193 | Sync mutable, no GC (ffi, fs, net, http, database, mcp, spec) |
| `nogc_async_mut/` | 148 | 29,972 | Async mutable, no GC (actors, async, threads, generators, mcp, llm) |
| `nogc_async_mut_noalloc/` | 79 | 12,829 | Baremetal, execution, memory, qemu |
| `gc_async_mut/` | 21 | 4,393 | GC + async (gpu, cuda, torch, pure ML library) |
| `database/` | 12 | 129 | Database interfaces |
| `ffi/` | 4 | 12 | FFI bridge utilities |
| `async/` | 3 | 6 | Async primitives |
| `sdn/` | 1 | 9 | SDN format |
| Root files | 10 | ~444 | `__init__.spl`, `text.spl`, `string_core.spl`, etc. |

#### Top 50 Modules by Size

| Module | Lines | Category | Key Types | Purpose |
|--------|-------|----------|-----------|---------|
| `bcrypt/core.spl` | 1,332 | Crypto | `BcryptHash` | Password hashing (bcrypt algorithm) |
| `cbor/core.spl` | 1,305 | Serialization | `CborEncoder`, `CborDecoder` | CBOR binary format |
| `skiplist_utils.spl` | 1,105 | Data Structures | `SkipList` | Probabilistic balanced tree |
| `graph/utilities.spl` | 978 | Algorithms | `Graph` | Dijkstra, BFS, DFS, topological sort |
| `linear_algebra/matrix_ops.spl` | 894 | Math | `Matrix` | Matrix operations |
| `set_utils.spl` | 777 | Collections | `Set` | Set operations (union, intersect) |
| `text_utils.spl` | 767 | String | - | Text processing helpers |
| `src/tooling/easy_fix/rules.spl` | 761 | Tooling | `FixRule` | Auto-fix rules for linter |
| `src/di.spl` | 744 | Infrastructure | `Container`, `Provider` | Dependency injection |
| `search_utils.spl` | 738 | Algorithms | - | Binary search, interpolation search |
| `amqp_utils.spl` | 738 | Networking | `AmqpConnection` | AMQP 0-9-1 protocol |
| `src/testing/mocking_advanced.spl` | 724 | Testing | `AdvancedMock` | Advanced mocking framework |
| `matrix_utils.spl` | 719 | Math | - | Matrix utilities (det, inv, eigen) |
| `udp_utils.spl` | 715 | Networking | `UdpSocket` | UDP networking |
| `src/infra.spl` | 712 | Infrastructure | - | Infrastructure patterns |
| `diff/utilities.spl` | 710 | Algorithms | `Differ` | Myers diff algorithm |
| `stats_utils.spl` | 700 | Math | - | Mean, median, stddev, correlation |
| `src/tensor.spl` | 697 | ML | `Tensor` | N-dimensional arrays for ML |
| `spec.spl` | 694 | Testing | `ExpectHelper` | SSpec BDD framework |
| `comparator_utils.spl` | 693 | Collections | - | Custom comparators |
| `binary_io.spl` | 690 | I/O | `BinaryReader`, `BinaryWriter` | Binary file I/O |
| `allocator.spl` | 683 | Memory | `Allocator`, `ArenaAllocator` | Custom memory allocators |
| `sdn/parser.spl` | 682 | Serialization | `SdnParser` | SDN format parser |
| `src/table.spl` | 682 | Data Structures | `Table` | Tabular data |
| `text.spl` | 627 | String | - | Core string operations |
| `json/core.spl` | 611 | Serialization | `JsonValue` | JSON parsing/encoding |
| `sdn/core.spl` | 573 | Serialization | `SdnValue` | SDN (Simple Data Notation) |
| `json/array_ops.spl` | 559 | Serialization | - | JSON array utilities |
| `http/client.spl` | 558 | Networking | `HttpClient` | HTTP client |
| `concurrent/thread_pool.spl` | 556 | Concurrency | `ThreadPool` | Thread pool executor |

#### Major Categories

| Category | Modules | Lines | Description |
|----------|---------|-------|-------------|
| **Data Structures** | ~85 | ~28,000 | Trees, graphs, skip lists, tries, ropes, heaps |
| **Algorithms** | ~45 | ~16,000 | Sorting, searching, graph, numeric, string matching |
| **Networking** | ~65 | ~20,000 | HTTP, TCP, UDP, WebSocket, MQTT, Kafka, AMQP |
| **Serialization** | ~35 | ~14,000 | JSON, CBOR, YAML, XML, Protobuf, Avro, MessagePack |
| **Cryptography** | ~40 | ~12,000 | AES, RSA, bcrypt, scrypt, JWT, TLS, hashing |
| **Math/ML** | ~30 | ~17,000 | Linear algebra, FFT, tensors, optimization |
| **Testing** | ~18 | ~6,000 | SSpec, mocking, benchmarking, property testing |
| **Utilities** | ~220 | ~45,000 | String, array, text, validation, encoding |
| **I/O** | ~30 | ~10,000 | File, binary, async I/O, streams |
| **Concurrency** | ~25 | ~8,000 | Threads, actors, channels, locks |

---

### 1.3 Applications (`src/app/` - 479 files, 75,423 lines)

**Purpose:** CLI tools, build system, MCP servers, language servers, test runners. 95 subdirectories.

#### Largest Applications (by file count/lines)

| Application | Files | Lines | Purpose |
|-------------|-------|-------|---------|
| `test_runner_new/` | 51 | 12,368 | Test runner & SDoctest |
| `io/` | 47 | 11,687 | I/O subsystem (CLI, JIT, window, audio) |
| `cli/` | 32 | 7,795 | CLI main & commands |
| `debug/` | 21 | 4,735 | Debugging tools |
| `test/` | 17 | 4,604 | Test extraction & scaffolding |
| `mcp/` | 11 | 4,045 | MCP servers (lazy CLI, debug, diag, protocol, query, tasks) |
| `lsp/` | 15 | 3,251 | Language Server Protocol |
| `dap/` | 13 | 3,188 | Debug Adapter Protocol |
| `doc/` | 10 | 2,699 | Documentation tools |
| `lsp.handlers/` | 7 | 2,094 | LSP handler implementations |
| `stats/` | 12 | 2,000 | Statistics & doc coverage |
| `test_daemon/` | 10 | 1,778 | Test daemon with caching & change detection |
| `leak_check/` | 9 | 1,251 | Leak detection tools |
| `compile/` | 8 | 1,011 | C translation & codegen |
| `feature_doc/` | 7 | 901 | Feature documentation generator |

#### New Applications (since 2026-02-16)
- `yank/main.spl` - Package yank/unpublish tool
- `test_daemon/manifest_daemon.spl` - Manifest-based test daemon

#### Key Application Details

**1. CLI (`cli/` - 32 files, 7,795 lines)**
- Entry point for `bin/simple` binary
- Command dispatch: build, test, run, compile
- Includes: `arch_check.spl`, `check_capsule.spl`, test commands

**2. Test Runner (`test_runner_new/` - 51 files, 12,368 lines)**
- SSpec test execution
- SDoctest (executable docs)
- Test report generation

**3. MCP Server (`mcp/` - 11 files, 4,045 lines)**
- Lazy protocol, CLI tools, debug tools, debug log tools
- Diagnostic tools, JSON handling, query tools
- Task management, test daemon tools

**4. Test Daemon (`test_daemon/` - 10 files, 1,778 lines)**
- Change detection and caching
- Dependency tracking
- QEMU broker, manifest daemon

---

### 1.4 Rust Seed Bootstrap (`src/compiler_rust/` - 1,800 .rs files, 482,983 lines)

**Purpose:** Rust implementation of the Simple compiler used to bootstrap the self-hosted Simple compiler. Contains both Rust source and a copy of the stdlib in `.spl` format.

| Component | Files | Lines | Purpose |
|-----------|-------|-------|---------|
| `compiler/src/` | 544 .rs | 194,251 | Core compiler (interpreter, values, builtins, macros) |
| `parser/src/` | 87 .rs | 33,626 | Parser (lexer, AST, patterns) |
| `lib/std/` | 712 .spl | 174,178 | Stdlib copy for Rust bootstrap |
| Other .rs | 826 | ~255,106 | Runtime, driver, tests, common utilities |

**Deleted `.disabled` directories (12 removed):**
- `browser.disabled`, `coverage.disabled`, `doctest.disabled`, `electron.disabled`
- `godot.disabled`, `graphics.disabled`, `ml.disabled`, `parser.disabled`
- `ui.disabled`, `units.disabled`, `unreal.disabled`, `web.disabled`

No `.disabled` directories remain anywhere in the codebase.

---

### 1.5 Other Source Directories

| Directory | Files | Lines | Purpose |
|-----------|-------|-------|---------|
| `src/compiler_cpp/` | 15 (C) | 16,208 | Generated C from Simple source (temporal bootstrap via CMake+Ninja) |
| `src/runtime/` | 48 (C) | 12,374 | C runtime (runtime.c/runtime.h linked by generated C++) |
| `src/i18n/` | 29 (.spl) | 4,801 | Internationalization |
| `src/lib/ffi/` | 4 (.spl) | 12 | FFI bridge utilities |

**Removed directories (no longer exist):**
- `src/compiler_core_legacy/` - Core compiler merged into `src/compiler/`
- `src/baremetal/` - Bare-metal runtime merged into library
- `src/remote/` - Remote execution merged into library

---

### 1.6 Test Suite (`test/` - 1,772 files, 327,890 lines)

| Directory | Files | Purpose |
|-----------|-------|---------|
| `test/unit/` | 1,318 | Unit tests |
| `test/feature/` | 326 | Feature tests |
| `test/integration/` | 47 | Integration tests |
| `test/system/` | 10 | System tests (including LLM live tests) |
| `test/perf/` | 7 | Performance benchmarks |
| `test/fuzz/` | 3 | Fuzz tests |
| Other | 61 | Fixtures, examples, manual, deploy, benchmarks |

---

## 2. Semantic Duplication Analysis

### CRITICAL DUPLICATIONS

#### 1. String/Text Processing (3-way overlap)

**Files involved:**
- `src/lib/text.spl` (627 lines)
- `src/lib/text_utils.spl` (767 lines)
- `src/lib/string_core.spl` (400+ lines)
- `src/lib/helpers.spl` (string functions, ~200 lines)

**Total:** ~2,000 lines
**Estimated duplication:** ~500-700 lines (25-35%)

**Overlapping functions:**
- Case conversion: `to_upper()`, `to_lower()`, `to_title_case()`, `to_snake_case()`, `to_camel_case()`
- Trimming: `trim()`, `trim_left()`, `trim_right()`, `trim_chars()`
- Splitting: `split()`, `split_lines()`, `split_whitespace()`
- Character checks: `is_alpha()`, `is_digit()`, `is_alnum()`, `is_space()`
- Padding: `pad_left()`, `pad_right()`, `center()`
- Validation: `is_email()`, `is_url()`, `is_path()`

**Why it happened:**
- Incremental stdlib development
- Different authors adding similar functions
- Copy-paste between modules

**Impact:** Medium-High (user confusion, maintenance burden)

---

#### 2. Array Operations (3-way overlap)

**Files involved:**
- `src/lib/array.spl` (350 lines)
- `src/lib/list_utils.spl` (250+ lines)
- `src/lib/collection_utils.spl` (estimated ~300 lines)
- `src/lib/json/array_ops.spl` (559 lines - JSON-specific)

**Total:** ~1,450 lines
**Estimated duplication:** ~300-400 lines (20-25%)

**Overlapping functions:**
- Flatten: `flatten()`, `flatten_deep()`
- Intersperse: `intersperse()`, `join_with()`
- Partition: `partition()`, `group_by()`
- Statistics: `sum()`, `product()`, `average()`, `median()`
- Chunking: `chunk()`, `chunk_by()`, `window()`
- Set operations: `union()`, `intersect()`, `difference()`

**Why it happened:**
- JSON library needed array ops, duplicated instead of importing
- List utilities grew organically separate from array.spl

**Impact:** Medium (maintenance, consistency)

---

#### 3. JSON Building (2 implementations)

**Files involved:**
- `src/lib/json/builder.spl` (354 lines) - **Recommended** ✅
- `src/lib/mcp_sdk/core/json.spl` (~200 lines) - Legacy ⚠️

**Pattern difference:**

**OOP Fluent API (`builder.spl`):**
```simple
val json = JsonBuilder()
    .add_string("name", "Alice")
    .add_int("age", 30)
    .build()
```

**Function Helpers (`json.spl`):**
```simple
val json = json_object([
    json_pair("name", json_string("Alice")),
    json_pair("age", json_int(30))
])
```

**Analysis:**
- `builder.spl` is more ergonomic (fluent API)
- `mcp_sdk/core/json.spl` used by MCP servers (legacy)
- Both do the same thing with different APIs

**Impact:** Low (isolated to MCP servers)

---

#### 4. Type Mappers (8 backends, 2 compilers)

**Files involved (compiler/):**
- `backend/llvm_type_mapper.spl` (304 lines)
- `backend/cranelift_type_mapper.spl` (234 lines)
- `backend/wasm_type_mapper.spl` (286 lines)
- `backend/interpreter_type_mapper.spl` (236 lines)
- `backend/cuda_type_mapper.spl` (317 lines)
- `backend/vulkan_type_mapper.spl` (384 lines)
- `backend/vhdl_type_mapper.spl` (213 lines)
- `backend/lean_type_mapper.spl` (~150 lines)

**Total:** ~2,774 lines
**Estimated structural overlap:** 30-40% (~830-1,110 lines)

**Common pattern:**
```simple
fn map_type(ty: TypeKind) -> BackendType:
    match ty:
        TypeKind.Int: backend_int_type()
        TypeKind.Float: backend_float_type()
        TypeKind.Bool: backend_bool_type()
        TypeKind.String: backend_string_type()
        # ... similar structure across all backends
```

**Why it exists:**
- Each backend has unique type requirements (LLVM IR vs SPIR-V vs PTX)
- Intentional duplication for backend isolation

**Recommendation:** Extract common `TypeMapper` trait when Full Simple trait system stabilizes.

**Impact:** Medium (maintenance burden when adding new types)

---

#### 5. Parser (multiple implementations)

**Files involved:**
- `src/compiler/10.frontend/core/parser.spl` + `parser_expr.spl` + `parser_primary.spl` - Self-hosted compiler parser
- `src/compiler_rust/parser/src/` (87 .rs files) - Rust bootstrap parser
- Various library parsers in `src/lib/`

**Why it exists:**
- Self-hosted parser in Simple for the production compiler
- Rust parser for bootstrapping
- Library parsers for user-facing parser combinators

**Common patterns:**
- Token consumption: `expect()`, `consume()`, `peek()`
- Expression parsing: `parse_expr()`, `parse_primary()`, `parse_binary_op()`
- Precedence climbing
- Error recovery

**Impact:** Medium (bootstrap requires dual implementation, but well-separated)

---

#### 6. Native Backend ISel (4 architectures)

**Files involved:**
- `compiler/70.backend/backend/native/isel_x86_64.spl` (669 lines)
- `compiler/70.backend/backend/native/isel_aarch64.spl` (601 lines)
- `compiler/70.backend/backend/native/isel_riscv64.spl` (595 lines)
- `compiler/70.backend/backend/native/isel_riscv32.spl` (615 lines)

**Plus encoding files:**
- `70.backend/backend/native/encode_x86_64.spl` (~600 lines)
- `70.backend/backend/native/encode_aarch64.spl` (~550 lines)
- `70.backend/backend/native/encode_riscv64.spl` (~550 lines)
- `70.backend/backend/native/encode_riscv32.spl` (~500 lines)

**Total:** 2,480 (isel) + 2,200 (encode) = **4,680 lines**
**Estimated overlap:** 60-70% (~2,800-3,275 lines)

**Common pattern (instruction selection):**
```simple
fn select_inst(mir: MirInst) -> MachInst:
    match mir.opcode:
        MirOpcode.Add:
            # x86: ADD reg, reg
            # ARM: ADD reg, reg, reg
            # RISC-V: ADD rd, rs1, rs2
        MirOpcode.Load:
            # x86: MOV reg, [mem]
            # ARM: LDR reg, [base, offset]
            # RISC-V: LW rd, offset(rs1)
        # ... 50+ opcodes with similar structure
```

**Why it exists:**
- Each architecture has different:
  - Instruction formats (2-operand vs 3-operand)
  - Register sets (16 vs 32 registers)
  - Addressing modes
  - Calling conventions

**Recommendation:** Extract ISA trait (very high risk, wait for trait system).

**Impact:** Very High Risk (core codegen, affects all native compilation)

---

#### 7. Testing Framework (scattered)

**Files involved:**
- `src/lib/spec.spl` (694 lines) - SSpec BDD framework
- `src/app/test_runner_new/test_runner_main.spl` (704 lines)
- `src/app/test_runner_new/test_runner_execute.spl` (624 lines)
- `src/lib/src/testing/mocking_advanced.spl` (724 lines)
- Various test utilities across stdlib

**Total:** ~3,000+ lines
**Estimated duplication:** ~200-300 lines (test setup/teardown patterns)

**Common patterns:**
- Test discovery
- Setup/teardown hooks
- Assertion helpers
- Mock frameworks

**Why it happened:**
- Incremental test infrastructure development
- Different testing styles (unit, integration, property)

**Impact:** Low-Medium (test code, not production code)

---

### MEDIUM DUPLICATIONS

#### 8. Lexer (2 implementations)

**Files involved:**
- `src/compiler/10.frontend/core/lexer.spl` - Self-hosted lexer (Simple)
- `src/compiler_rust/parser/src/` - Rust bootstrap lexer

**Why it exists:** Bootstrap requires both Simple and Rust implementations

**Impact:** Medium (maintenance burden, but well-separated by language)

---

#### 9. Validation Predicates (scattered)

**Files involved:**
- `src/lib/math.spl` - `is_finite()`, `is_nan()`, `is_infinite()`
- `src/lib/validation_utils.spl` - `is_email()`, `is_url()`, `is_path()`
- `src/lib/text.spl` - `is_alpha()`, `is_digit()`, `is_alnum()`

**Total:** ~400-500 lines scattered
**Estimated duplication:** ~100-150 lines (similar validation patterns)

**Why it happened:** No central validation module

**Impact:** Low (small functions, easy to consolidate)

---

#### 10. Option/Result Helpers (2 locations)

**Files involved:**
- `src/lib/option_helpers.spl` (~200 lines)
- `src/lib/functional.spl` (Option/Result monadic operations, ~150 lines)

**Overlap:** ~50-80 lines (map, flatMap, filter, getOrElse)

**Why it happened:** Functional programming utilities grew separate from option helpers

**Impact:** Low (minimal duplication)

---

### LOW-PRIORITY DUPLICATIONS

#### 11. FFI Specs (tool-generated)

**Files:** 41 files in `src/app/ffi_gen.specs/` (~6,600 lines)

**Pattern:** All follow similar structure (enum specs, function specs, struct specs)

**Why it exists:** Auto-generated by FFI generator tool

**Recommendation:** Keep as-is (regenerate instead of manually editing)

**Impact:** Very Low (tool output)

---

## 3. Merger Recommendations

### Recommendation 1: Consolidate String Processing

**Priority:** P1 High
**Files to merge:**
- `src/lib/text.spl` (627 lines)
- `src/lib/text_utils.spl` (767 lines)
- `src/lib/string_core.spl` (~400 lines)
- `src/lib/helpers.spl` (string functions only, ~200 lines)

**Target:** `src/lib/text.spl` (expanded to ~1,200 lines)

**Expected reduction:** ~800 lines (from 2,000 to ~1,200 net)

**Risk:** Medium (need to update 150+ import statements)

**Action plan:**
1. **Week 1, Day 1-2:** Create comprehensive test suite
   - Write tests for all string functions across all 4 files
   - Verify behavior matches exactly
   - Target: 200+ tests covering edge cases

2. **Week 1, Day 3:** Merge case conversion functions
   - Move `text_utils.spl` case functions → `text.spl`
   - Update exports in `text.spl`
   - Run tests (expect 200+ passing)

3. **Week 1, Day 4:** Merge character predicates
   - Move `is_alpha()`, `is_digit()`, etc. → `text.spl`
   - Consolidate with existing predicates
   - Verify no duplicates

4. **Week 1, Day 5:** Merge trimming/padding
   - Move `text_utils.spl` trim/pad → `text.spl`
   - Consolidate with `string_core.spl` versions

5. **Week 2, Day 1-2:** Update imports
   - Search: `use std.text_utils.{`
   - Replace: `use std.text.{`
   - Update ~150 files in test/ and src/
   - Run full test suite after each batch

6. **Week 2, Day 3:** Deprecate old files
   - Mark `text_utils.spl` as deprecated (add warning comment)
   - Remove string functions from `helpers.spl`
   - Keep `string_core.spl` for now (internal APIs)

7. **Week 2, Day 4-5:** Verification
   - Run full test suite (full test suite)
   - Check no regressions
   - Update documentation

**Files to update:** ~150 files with imports

**Rollback plan:** Keep `text_utils.spl` as deprecated forwarding module for 1 release cycle.

---

### Recommendation 2: Consolidate Array Operations

**Priority:** P1 High
**Files to merge:**
- `src/lib/array.spl` (350 lines)
- `src/lib/list_utils.spl` (~250 lines)
- `src/lib/collection_utils.spl` (~300 lines estimated)

**Leave separate:** `src/lib/json/array_ops.spl` (JSON-specific)

**Target:** `src/lib/array.spl` (expanded to ~600 lines)

**Expected reduction:** ~300 lines (from 900 to ~600 net)

**Risk:** Low-Medium (isolated to collection operations)

**Action plan:**
1. **Day 1:** Create test suite (100+ tests)
2. **Day 2:** Merge `flatten()`, `intersperse()`, `partition()`
3. **Day 3:** Merge statistics functions (`sum`, `mean`, `median`)
4. **Day 4:** Update imports (~80 files)
5. **Day 5:** Verification & documentation

**Rollback plan:** Keep `list_utils.spl` as forwarding module.

---

### Recommendation 3: Migrate MCP JSON to JsonBuilder

**Priority:** P1 High
**Files to merge:**
- `src/lib/mcp_sdk/core/json.spl` (~200 lines) - **Remove**
- Use `src/lib/json/builder.spl` (354 lines) instead

**Target:** All MCP servers use JsonBuilder fluent API

**Expected reduction:** ~200 lines

**Risk:** Low (isolated to MCP servers, 5 files affected)

**Action plan:**
1. **Day 1:** Update `mcp/fileio_main.spl`
   - Replace `json_object()` calls with `JsonBuilder().add_*().build()`
   - Test MCP server (manual verification)

2. **Day 2:** Update `mcp/debug_tools.spl`
   - Same pattern
   - Test debug MCP

3. **Day 3:** Update `mcp_jj/tools_jj.spl` and `tools_git.spl`
   - Same pattern
   - Test Jujutsu MCP

4. **Day 4:** Remove `mcp_sdk/core/json.spl`
   - Verify no remaining imports
   - Delete file

5. **Day 5:** Documentation
   - Update MCP development guide
   - Add JsonBuilder example

**Files to update:** 5 MCP server files

**Rollback plan:** Keep old `json.spl` in git history, easy to restore.

---

### Recommendation 4: Extract Validation Module

**Priority:** P2 Medium
**Files to consolidate:**
- `src/lib/math.spl` (numeric validation)
- `src/lib/validation_utils.spl` (string validation)
- `src/lib/text.spl` (character validation)

**Target:** New `src/lib/validation.spl` (~300 lines)

**Expected reduction:** ~100-150 lines

**Risk:** Low (pure functions, no side effects)

**Action plan:**
1. **Week 1:** Create `src/lib/validation.spl`
   - Move all `is_*()` predicates
   - Organize by category (numeric, string, character, format)

2. **Week 2:** Update imports
   - Search for `is_email`, `is_url`, `is_nan`, etc.
   - Update ~60 files

3. **Week 3:** Deprecate old locations
   - Keep forwarding functions for 1 release

**Files to update:** ~60 files

---

### Recommendation 5: Consolidate Phase Files

**Priority:** P2 Medium
**Files to merge:**
- `bidir_phase1a-d.spl` (4 files) → `bidirectional_checking.spl`
- `associated_types_phase4a-d.spl` (4 files) → `associated_types.spl`
- `higher_rank_poly_phase5a-d.spl` (4 files) → `higher_rank_polymorphism.spl`
- `variance_phase6a-d.spl` (4 files) → `variance_checking.spl`
- `macro_checker_phase7a-c.spl` (3 files) → `macro_validation.spl`
- `const_keys_phase8a-c.spl` (3 files) → `const_keys.spl`
- `simd_phase9a-c.spl` (3 files) → `simd_analysis.spl`

**Total:** 27 files → 7 files

**Expected reduction:** ~8,000 lines (from ~20,000 to ~12,000)

**Risk:** Low (development history, not critical path)

**Action plan:**
1. **Week 1:** Consolidate bidirectional checking
   - Merge phase1a-d into single file
   - Keep most recent implementation
   - Add comments explaining evolution

2. **Week 2:** Consolidate associated types, higher-rank poly

3. **Week 3:** Consolidate variance, macros, const keys, SIMD

4. **Week 4:** Move originals to `doc/design/phases/` for history

**Alternative:** Keep as-is (documents incremental development)

**Decision:** Consult with team (value of history vs. reduced complexity)

---

### Recommendation 6: Type Mapper Abstraction

**Priority:** P3 Long-term (wait for trait system)
**Files affected:** 16 type mapper files (~3,574 lines)

**Expected reduction:** ~1,500 lines (after trait system stabilizes)

**Risk:** High (affects all backends)

**Proposed design:**
```simple
trait TypeMapper:
    fn map_int(self) -> BackendType
    fn map_float(self) -> BackendType
    fn map_bool(self) -> BackendType
    fn map_string(self) -> BackendType
    fn map_struct(self, fields: [Field]) -> BackendType
    fn map_enum(self, variants: [Variant]) -> BackendType

class LLVMTypeMapper:
    impl TypeMapper:
        fn map_int(self): llvm_i64_type()
        fn map_float(self): llvm_double_type()
        # ...
```

**Action plan:** Defer until Full Simple trait system is production-ready.

**Timeline:** 6+ months

---

### Recommendation 7: ISA Abstraction Layer

**Priority:** P3 Long-term (very high risk)
**Files affected:** 8 ISA files (~4,680 lines)

**Expected reduction:** ~1,500 lines

**Risk:** Very High (affects all native compilation)

**Proposed design:**
```simple
trait ISA:
    fn select_add(self, dest: Reg, src1: Reg, src2: Reg) -> MachInst
    fn select_load(self, dest: Reg, addr: Addr) -> MachInst
    fn encode_inst(self, inst: MachInst) -> [u8]
    # ... 50+ methods

class X86_64ISA:
    impl ISA:
        fn select_add(self, dest, src1, src2):
            # x86: ADD reg, reg (2-operand, dest=src1)
        fn encode_inst(self, inst):
            # ModRM encoding, REX prefix, etc.
```

**Action plan:**
1. Wait for Full Simple trait system (6+ months)
2. Design ISA trait hierarchy (1 month)
3. Implement for x86-64 as pilot (1 month)
4. Comprehensive testing on all platforms (1 month)
5. Gradual migration with fallbacks (2 months)

**Total timeline:** 11+ months from trait system completion

**Decision:** Only attempt after trait system is mature (2-3 releases)

---

## 4. Removal Candidates

### Completely Redundant (Exact Duplicates)

#### 1. `src/lib/pure/parser_old.spl` (858 lines)

**Reason:** Superseded by `pure/parser.spl`
**Risk:** Very Low (not imported anywhere)
**Action:** Delete immediately
**Savings:** 858 lines

---

#### 2. Deprecated Helper Functions

**Candidates:**
- String functions in `src/lib/helpers.spl` (after string consolidation)
- Old validation predicates (after validation module)

**Savings:** ~200-300 lines

---

### Can Be Auto-Generated

#### 3. FFI Specs (consider regeneration)

**Files:** 41 files in `ffi_gen.specs/` (~6,600 lines)

**Action:** Verify these are tool output, not hand-edited
- If tool output: Keep as-is (regenerate when needed)
- If hand-edited: Migrate edits to tool config

**Recommendation:** Document which files are generated vs. hand-edited

---

### Old/Unused Implementations

#### 4. Legacy Parser/Lexer Code

**Candidates:**
- Any files marked with `_old`, `_legacy`, `_deprecated` suffixes

**Action:** Audit and remove after verification

**Estimated savings:** ~1,000-2,000 lines

---

## 5. Architecture Improvements

### Module Hierarchy

**Current state:** `src/lib/` is now organized by mutation/GC category:

```
src/lib/
  common/                  # 676 files - Pure functions, no mutation
  nogc_sync_mut/           # 592 files - Sync mutable, no GC
  nogc_async_mut/          # 148 files - Async mutable, no GC
  gc_async_mut/            #  21 files - GC + async (GPU, ML)
  nogc_async_mut_noalloc/  #  79 files - Baremetal, no alloc
  database/                #  12 files - Database interfaces
  ffi/                     #   4 files - FFI bridge
  async/                   #   3 files - Async primitives
  sdn/                     #   1 file  - SDN format
```

**Note:** This category-based organization was adopted since 2026-02-16. Within each category, modules are organized by domain (e.g., `common/json/`, `common/crypto/`, `nogc_sync_mut/mcp/`).

**Remaining improvement:** Within `common/` (676 files), some naming inconsistencies persist (`*_utils.spl` overuse).

---

### Naming Conventions

**Current issue:** Inconsistent suffixes (`_utils`, `_helpers`, `_core`)

**Proposal:** Standardize naming

| Old Pattern | New Pattern | Rationale |
|-------------|-------------|-----------|
| `string_utils.spl` | `text.spl` | Consolidate, remove redundant suffix |
| `text_utils.spl` | `text.spl` or merge into `text.spl` | Remove suffix |
| `array_ops.spl` | `array.spl` | "ops" is redundant |
| `*_helpers.spl` | `*_support.spl` or merge | Clarify purpose |
| `*_core.spl` | `*_internal.spl` | Internal APIs |

**Benefits:**
- Consistent naming
- Easier to remember
- Less clutter

**Risk:** Medium (breaks imports)

---

### Import Patterns

**Current issue:** Circular dependencies in some modules

**Recommendation:**
1. Identify circular imports: `grep -r "^use " src/ | # analyze dependencies`
2. Break cycles by extracting interfaces or moving shared code to `core/`
3. Document dependency hierarchy in `doc/architecture/module_dependencies.md`

---

### Code Organization

**Current issue:** Overuse of `*_utils.spl` suffix (60+ files)

**Proposal:**
- `*_utils.spl` → primary module name (e.g., `string_utils.spl` → `text.spl`)
- Or organize into subdirectories (e.g., `collections/utils/`)

**Benefits:** Clearer module purpose

---

## 6. Priority Matrix

| Priority | Items | LOC Savings | Risk | Effort | ROI |
|----------|-------|-------------|------|--------|-----|
| **P1 High** | 5 | ~2,300 | Low | 2 weeks | 115 lines/day |
| **P2 Medium** | 10-15 | ~9,500 | Med | 2 months | 120 lines/day |
| **P3 Low** | 5-10 | ~3,000 | High | 12+ months | 8 lines/day |
| **Total** | 20-30 | ~14,800 | - | 14+ months | - |

### P1 High Priority (Quick Wins)

| Item | LOC Savings | Effort | Risk | Files Affected |
|------|-------------|--------|------|----------------|
| 1. Consolidate string processing | ~800 | 2 weeks | Med | ~150 |
| 2. Consolidate array operations | ~300 | 1 week | Low | ~80 |
| 3. Migrate MCP to JsonBuilder | ~200 | 1 week | Low | 5 |
| 4. Remove `parser_old.spl` | ~858 | 1 hour | Very Low | 1 |
| 5. Extract validation module | ~150 | 1 week | Low | ~60 |
| **Total P1** | **~2,308** | **5 weeks** | - | **~296** |

**Timeline:** 5 weeks (1.25 months)
**ROI:** 2,308 lines / 25 days = **92 lines/day**

---

### P2 Medium Priority

| Item | LOC Savings | Effort | Risk | Files Affected |
|------|-------------|--------|------|----------------|
| 6. Consolidate phase files | ~8,000 | 4 weeks | Low | 27 |
| 7. Reorganize std/ hierarchy | ~500 (indirect) | 3 weeks | Med | ~900 |
| 8. Standardize naming conventions | ~200 (indirect) | 2 weeks | Med | ~100 |
| 9. Extract builder utilities | ~500 | 1 week | Low | 8 |
| 10. Extract validation framework | ~400 | 2 weeks | Med | ~28 |
| **Total P2** | **~9,600** | **12 weeks** | - | **~1,063** |

**Timeline:** 12 weeks (3 months)
**ROI:** 9,600 lines / 60 days = **160 lines/day**

---

### P3 Low Priority (Long-term)

| Item | LOC Savings | Effort | Risk | Files Affected |
|------|-------------|--------|------|----------------|
| 11. Type mapper abstraction | ~1,500 | 2 months | High | 16 |
| 12. ISA abstraction layer | ~1,500 | 5 months | Very High | 8 |
| **Total P3** | **~3,000** | **7 months** | - | **24** |

**Prerequisite:** Full Simple trait system must be stable
**Timeline:** 7 months after trait system ready
**ROI:** 3,000 lines / 140 days = **21 lines/day**

---

### Work That Should NOT Be Done

#### 1. Lexer/Parser Bootstrap Duplication

**Files:** `compiler/10.frontend/core/lexer.spl` (Simple), `compiler_rust/parser/src/` (Rust)

**Reason:** Required for self-hosting bootstrap (Rust seeds Simple)
**Status:** Documented, intentional
**Decision:** Keep as-is (two different languages, necessary for bootstrap)

---

#### 2. Backend-Specific Code (before trait system)

**Files:** Type mappers, ISA encoders

**Reason:** Each backend has unique requirements
**Decision:** Wait for trait system to stabilize

---

#### 3. Specialized Parsers

**Files:** `sdn/parser.spl`, `json/parser.spl`, `xml/parser.spl`, `html/parser.spl`

**Reason:** Different grammars and requirements
**Decision:** Keep separate (not duplication, different purposes)

---

## 7. Implementation Roadmap

### Phase 1: Quick Wins (5 weeks)

**Week 1-2: String Consolidation**
- Day 1-2: Create test suite (200+ tests)
- Day 3-5: Merge case conversion, character predicates
- Day 6-10: Update imports (~150 files)

**Week 3: Array Consolidation**
- Day 1: Create test suite (100+ tests)
- Day 2-3: Merge functions
- Day 4-5: Update imports (~80 files)

**Week 4: MCP JsonBuilder Migration**
- Day 1-4: Update 5 MCP servers
- Day 5: Remove old `mcp_sdk/core/json.spl`

**Week 5: Cleanup**
- Day 1: Remove `parser_old.spl`
- Day 2-5: Extract validation module

**Deliverables:**
- ~2,300 lines removed
- ~300 files updated
- Full test suite passing (full test suite)

**Dependencies:** None

**Rollback plan:** Keep deprecated modules for 1 release cycle

---

### Phase 2: Medium-term Improvements (12 weeks)

**Week 1-4: Phase File Consolidation**
- Week 1: Merge bidirectional checking (4 files → 1)
- Week 2: Merge associated types, higher-rank poly (8 files → 2)
- Week 3: Merge variance, macros (7 files → 2)
- Week 4: Move originals to `doc/design/phases/`

**Week 5-7: Stdlib Reorganization**
- Week 5: Design new hierarchy, create directories
- Week 6: Move files, create forwarding modules
- Week 7: Update imports gradually

**Week 8-9: Naming Standardization**
- Week 8: Rename `*_utils.spl` files
- Week 9: Update imports

**Week 10: Builder Utilities**
- Extract common builder patterns

**Week 11-12: Validation Framework**
- Design `ValidationContext` class
- Migrate 1-2 validators as pilot

**Deliverables:**
- ~9,600 lines removed (indirect benefits from organization)
- Cleaner module hierarchy
- Consistent naming

**Dependencies:** Phase 1 complete

**Rollback plan:** Forwarding modules for 2 release cycles

---

### Phase 3: Long-term Refactoring (7+ months, after trait system)

**Prerequisite:** Full Simple trait system must be production-ready

**Month 1-2: Type Mapper Abstraction**
- Month 1: Design `TypeMapper` trait
- Month 2: Implement for 2 backends as pilot

**Month 3-7: ISA Abstraction Layer**
- Month 3: Design ISA trait hierarchy
- Month 4: Implement for x86-64
- Month 5: Comprehensive testing
- Month 6-7: Gradual migration (ARM, RISC-V)

**Deliverables:**
- ~3,000 lines removed
- Trait-based backend architecture

**Dependencies:**
- Trait system stable (2-3 releases)
- Phase 1 and 2 complete

**Rollback plan:** Keep old implementations in parallel, feature flag

---

### Test Requirements

**For each phase:**

1. **Regression Testing**
   - Run full test suite (full test suite)
   - Zero tolerance for failures
   - Run after each batch of changes (not just at end)

2. **Import Verification**
   - Script to verify all imports resolve
   - Check for missing symbols
   - Validate no circular dependencies

3. **Performance Testing**
   - Benchmark key operations (parsing, compilation)
   - Ensure no performance regressions
   - Target: <5% slowdown acceptable

4. **Documentation Updates**
   - Update import examples in guides
   - Regenerate API documentation
   - Update CLAUDE.md if stdlib changes

---

### Rollback Plan

**If Phase 1 goes wrong:**
1. Revert commits (use `jj` undo)
2. Restore deprecated modules from git history
3. Regenerate forwarding modules
4. Re-run tests to verify restoration

**If Phase 2 goes wrong:**
1. Forwarding modules should still work
2. Revert directory moves
3. Restore original imports

**If Phase 3 goes wrong:**
1. Feature flag to disable new trait-based backends
2. Keep old implementations in parallel
3. Gradual cutover (opt-in initially)

---

## 8. Summary Statistics & Health Metrics

### Codebase Health (2026-03-02)

| Metric | Value | Target | Status |
|--------|-------|--------|--------|
| **Total .spl Files (src/)** | 3,708 | - | - |
| **Total .spl Lines (src/)** | 779,948 | - | - |
| **Rust Lines** | 482,983 | - | Bootstrap seed |
| **C Lines** | 28,582 | - | Bootstrap + runtime |
| **Test Files** | 1,772 | - | - |
| **Test Lines** | 327,890 | - | - |
| **Compiler Layers** | 17 | - | Numbered 00-99 |
| **Self-Hosting** | Stage 3 | Complete | Fixed-point reached |
| **Disabled Lib Dirs Deleted** | 12 | 0 remaining | Cleanup complete |

### Architecture Overview

| Component | Files | Lines | Language | Role |
|-----------|-------|-------|----------|------|
| **Self-hosted compiler** | 918 .spl | 207,912 | Simple | Production compiler |
| **Standard library** | 1,546 .spl | 317,086 | Simple | `use std.X` imports |
| **Applications** | 479 .spl | 75,423 | Simple | CLI, MCP, LSP, test runner |
| **Rust bootstrap** | 1,800 .rs | 482,983 | Rust | Seed compiler for bootstrapping |
| **Rust stdlib copy** | 712 .spl | 174,178 | Simple | Stdlib for Rust bootstrap |
| **C bootstrap** | 15 .c | 16,208 | C | Generated C dispatcher |
| **C runtime** | 48 .c/.h | 12,374 | C | Runtime linked by generated C++ |
| **i18n** | 29 .spl | 4,801 | Simple | Internationalization |
| **Tests** | 1,772 .spl | 327,890 | Simple | Unit, integration, system, feature |

**Recommendation:** Focus on Phase 1 refactoring (highest ROI, lowest risk)

---

## 9. Key Findings & Recommendations

### Architectural Insights

1. **Self-Hosting is Complete**
   - Stage 3 reached: Simple compiles itself (fixed-point)
   - `compiler_core_legacy/` has been merged/removed
   - Rust seed compiler bootstraps the Simple compiler
   - **Status:** Production-ready self-hosted compiler

2. **Numbered Compiler Layers Are Well-Organized**
   - 17 layers (00-99) with clear dependency ordering
   - Layer numbers stripped for import paths
   - Legacy empty dirs remain as remnants but contain no files
   - **Recommendation:** Clean up empty legacy dirs when convenient

3. **Standard Library is Comprehensive and Well-Categorized**
   - 1,546 files, 317K lines organized by mutation/GC category
   - `common/` (676 files) - Pure functions, largest category
   - `nogc_sync_mut/` (592 files) - Sync mutable operations
   - `nogc_async_mut/` (148 files) - Async operations including MCP
   - **Recommendation:** Continue category-based organization

4. **Backend Architecture is Sound**
   - Backends in `70.backend/` (186 files, 50K lines)
   - Type mapper duplication is acceptable for now
   - ISA encoder duplication is high-risk to change
   - **Recommendation:** Wait for trait system before abstracting

5. **12 Disabled Library Directories Cleaned Up**
   - browser, coverage, doctest, electron, godot, graphics, ml, parser, ui, units, unreal, web
   - All removed from `compiler_rust/lib/std/src/`
   - No `.disabled` directories remain

### Strengths

- Well-organized numbered compiler layers
- Self-hosting compiler with fixed-point bootstrap
- Comprehensive standard library (1,546 files)
- Category-based library organization (common, nogc_sync_mut, etc.)
- MCP handler adapters properly placed in async layer
- Clean codebase (no disabled directories remaining)

### Weaknesses

- String/array utilities scattered across library
- Some legacy empty directories in compiler/
- Some inconsistent naming (`*_utils` overuse in common/)

### Maintenance Burden

**High-Maintenance Areas:**
1. Rust bootstrap ↔ Simple compiler synchronization
2. Phase files (27 files, manual tracking)
3. Backend type mappers (16 files, backend-specific changes)
4. ISA encoders (8 files, architecture-specific)

**Low-Maintenance Areas:**
1. Core interpreter (well-abstracted)
2. Standard library (mostly independent)
3. Applications (clear separation of concerns)
4. Test suite (comprehensive, stable)

---

## 10. Actionable Next Steps

### Immediate Actions (This Week)

1. **Remove `parser_old.spl`** (1 hour)
   - Verify not imported: `grep -r "pure.parser_old" src/ test/`
   - Delete file
   - Commit: "refactor: Remove legacy pure/parser_old.spl (858 lines)"

2. **Start String Consolidation Test Suite** (2 days)
   - Create `test/unit/std/string_comprehensive_spec.spl`
   - Test all functions from text.spl, text_utils.spl, string_core.spl
   - Target: 200+ tests

### This Month (Phase 1 Start)

3. **Week 1-2: String Consolidation**
   - Follow Recommendation 1 action plan
   - Update ~150 import statements
   - Verify full test suite still pass

4. **Week 3: Array Consolidation**
   - Follow Recommendation 2 action plan
   - Update ~80 import statements

5. **Week 4: MCP JsonBuilder Migration**
   - Follow Recommendation 3 action plan
   - Update 5 MCP server files

### Next Quarter (Phase 1 + Phase 2 Start)

6. **Month 2: Extract Validation Module**
   - Create `src/lib/validation.spl`
   - Update ~60 import statements

7. **Month 3: Consolidate Phase Files**
   - Follow Recommendation 5 action plan
   - Merge 27 files → 7 files

8. **Month 4: Start Stdlib Reorganization**
   - Design new hierarchy
   - Create directories, forwarding modules

### Long-term (6+ months)

9. **After Trait System Stabilizes:**
   - Type mapper abstraction (Phase 3)
   - ISA abstraction layer (Phase 3, very high risk)

---

## Appendix: Quick Reference

### Search Commands

```bash
# Find all .spl files
find src/ -name "*.spl" -not -path "*/compiler/mdsoc/*" -not -path "src/std/*"

# Count lines by directory
for dir in src/*/; do
  echo "$(basename "$dir"): $(find "$dir" -name "*.spl" -exec wc -l {} + 2>/dev/null | tail -1)"
done

# Count compiler layer files
for dir in src/compiler/[0-9]*/; do
  count=$(find "$dir" -name "*.spl" | wc -l)
  echo "$(basename "$dir"): $count files"
done

# Find duplicate function names across files
grep -rh "^fn " src/ --include="*.spl" | sort | uniq -c | sort -rn | head -30

# Find all imports of a module
grep -r "use std.text" src/ test/

# Find all type mapper files
find src/compiler/70.backend/ -name "*_type_mapper.spl"

# Count ISA files
find src/compiler/70.backend/backend/native -name "isel_*.spl" -o -name "encode_*.spl"
```

### Key Files to Review

**Documentation:**
- `CLAUDE.md` - Development guide
- `doc/guide/syntax_quick_reference.md` - Language syntax

**Core Implementation:**
- `src/compiler/10.frontend/core/parser.spl` - Self-hosted parser
- `src/compiler/10.frontend/core/lexer.spl` - Self-hosted lexer
- `src/compiler/80.driver/` - Compiler driver & pipeline
- `src/app/cli/` - CLI entry point & commands
- `src/app/mcp/` - MCP server implementation

**Compiler Layers (key entry points):**
- `src/compiler/10.frontend/` - Frontend (lexer, parser, AST, tree-sitter)
- `src/compiler/30.types/` - Type inference & type system
- `src/compiler/70.backend/` - All backends (LLVM, C, Cranelift, WASM, Native)
- `src/compiler/85.mdsoc/` - MDSOC capsule system
- `src/compiler/90.tools/` - Developer tools (lint, AOP, coverage, query)

**Duplication Hotspots:**
- `src/lib/common/text.spl`, string utilities - String processing
- `src/compiler/70.backend/backend/*_type_mapper.spl` - Backend type mappers
- `src/compiler/70.backend/backend/native/isel_*.spl` - ISA instruction selection

---

**Document Version:** 3.0
**Date:** 2026-03-02
**Author:** Claude Opus 4.6
**Status:** Comprehensive inventory updated to reflect numbered compiler layers, deleted legacy dirs, self-hosting completion
**Previous Version:** 2.0 (2026-02-16, Claude Sonnet 4.5)
**Next Review:** After Phase 1 completion
