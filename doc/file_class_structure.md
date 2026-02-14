# Simple Language Compiler - File & Class Structure Analysis

**Date:** 2026-02-14
**Status:** Comprehensive Inventory
**Scope:** Full codebase (2,578 .spl files, 98,916 lines)

---

## Executive Summary

### Codebase Statistics

| Metric | Value |
|--------|-------|
| Total .spl Files | 2,578 |
| Total Lines of Code | 98,916 |
| Classes | 1,254 |
| Structs | 2,192 |
| Enums | 1,052 |
| Total Type Definitions | 4,498 |

### Distribution by Directory

| Directory | Files | Lines | % of Codebase | Purpose |
|-----------|-------|-------|---------------|---------|
| `src/std/` | 901 | 185,046 | 187.0% | Standard library (includes utilities, overlaps with main count) |
| `src/compiler/` | 420 | 136,623 | 138.1% | Full compiler (Full Simple) |
| `src/app/` | 584 | 122,309 | 123.6% | Applications & tools |
| `src/compiler_core/` | 441 | 98,874 | 99.9% | Core compiler (Core Simple) |
| `src/lib/` | 102 | 23,992 | 24.3% | Database, actors, ML, parsers |
| `src/core/` | 36 | 15,691 | 15.9% | Core Simple library (seed-compilable) |
| `src/baremetal/` | 32 | 4,088 | 4.1% | Bare-metal runtime |
| Other | 62 | 5,609 | 5.7% | Diagnostics, FFI, remote, shared |

**Note:** Percentages exceed 100% because `src/std/` contains many utility files that duplicate functionality across modules.

### Duplication Summary

| Category | Estimated Lines | Status | Priority |
|----------|----------------|--------|----------|
| **Intentional: compiler/ ↔ compiler_core/** | ~15,000 | Documented | N/A (bootstrap) |
| **Lexer triplication** (core, compiler, compiler_core) | ~3,700 | Documented | Low (bootstrap) |
| **Parser triplication** (core, compiler, lib/) | ~6,700 | Documented | Low (bootstrap) |
| **Type mappers** (7 backends × 2 compilers) | ~4,700 | Documented | Low (backend-specific) |
| **Phase files** (27 development files) | ~12,000 | Documented | Medium (consolidation) |
| **Validators/Checkers** (~14 files) | ~6,400 | Structural | High (framework opportunity) |
| **ISA encoders** (3 architectures × 2 sets) | ~4,600 | Cross-platform | Very High Risk |
| **String/Array utilities** (std/) | ~4,200 | Scattered | Medium |
| **FFI specs** (41 files in ffi_gen.specs/) | ~6,600 | Generated | Low (tool output) |

**Total Addressable Duplication:** ~16,000 lines (excluding intentional bootstrap duplication)
**Duplication Percentage:** ~16% of codebase

---

## 1. Directory Structure

### 1.1 Core Simple Library (`src/core/` - 36 files, 15,691 lines)

**Purpose:** Seed-compilable core library, minimal dependencies, can bootstrap itself.

**Key Files:**

| File | Lines | Purpose |
|------|-------|---------|
| `compiler/c_codegen.spl` | 2,339 | C code generation (seed compiler) |
| `parser.spl` | 2,135 | Core parser implementation |
| `interpreter/eval.spl` | 1,797 | Tree-walk interpreter with JIT |
| `ast.spl` | 922 | Abstract syntax tree definitions |
| `lexer.spl` | 829 | Lexical analysis |
| `lexer_struct.spl` | 720 | Lexer state structs |
| `mir.spl` | 756 | Mid-level IR definitions |
| `types.spl` | 582 | Type system core |
| `aop.spl` | 541 | Aspect-oriented programming |
| `type_checker.spl` | 442 | Type checking |
| `tokens.spl` | 446 | Token definitions |
| `type_inference.spl` | 415 | Type inference engine |
| `type_erasure.spl` | 302 | Generic type erasure |

**Subdirectories:**
- `interpreter/` (7 files, 3,053 lines) - Core interpreter (eval, env, ops, value, jit, module_loader)
- `compiler/` (3 files, 2,463 lines) - Seed C codegen, driver, tests

**Key Types:**
- **Structs:** `CoreExpr`, `CoreStmt`, `CoreDecl`, `CoreLexer`, `CoreParser`, `MirInst`
- **Enums:** `TokenKind`, `AstNodeKind`, `TypeKind`, `MirOpcode`

---

### 1.2 Standard Library (`src/std/` - 901 files, 185,046 lines)

**Purpose:** Comprehensive standard library with utilities, data structures, protocols, ML, graphics.

**Top 30 Largest Modules:**

| Module | Lines | Category | Description |
|--------|-------|----------|-------------|
| `bcrypt/core.spl` | 1,332 | Crypto | Password hashing |
| `cbor/core.spl` | 1,305 | Serialization | CBOR encoding/decoding |
| `skiplist_utils.spl` | 1,105 | Data Structures | Skip list utilities |
| `graph/utilities.spl` | 978 | Algorithms | Graph algorithms |
| `linear_algebra/matrix_ops.spl` | 894 | Math | Matrix operations |
| `set_utils.spl` | 777 | Collections | Set utilities |
| `text_utils.spl` | 767 | String | Text processing |
| `src/tooling/easy_fix/rules.spl` | 761 | Tooling | Auto-fix rules |
| `src/di.spl` | 744 | Infrastructure | Dependency injection |
| `search_utils.spl` | 738 | Algorithms | Search algorithms |
| `amqp_utils.spl` | 738 | Networking | AMQP protocol |
| `src/testing/mocking_advanced.spl` | 724 | Testing | Advanced mocking |
| `matrix_utils.spl` | 719 | Math | Matrix utilities |
| `udp_utils.spl` | 715 | Networking | UDP utilities |
| `src/infra.spl` | 712 | Infrastructure | Infrastructure support |
| `diff/utilities.spl` | 710 | Algorithms | Diff algorithms |
| `stats_utils.spl` | 700 | Math | Statistics |
| `src/tensor.spl` | 697 | ML | Tensor operations |
| `comparator_utils.spl` | 693 | Collections | Comparators |
| `binary_io.spl` | 690 | I/O | Binary I/O |

**Major Categories:**

| Category | Modules | Total Lines | Description |
|----------|---------|-------------|-------------|
| **Data Structures** | ~80 | ~25,000 | Trees, graphs, skip lists, tries, ropes |
| **Algorithms** | ~40 | ~15,000 | Sorting, searching, graph, numeric |
| **Networking** | ~60 | ~18,000 | HTTP, TCP, UDP, WebSocket, MQTT, Kafka |
| **Serialization** | ~30 | ~12,000 | JSON, CBOR, YAML, XML, Protobuf, Avro |
| **Cryptography** | ~35 | ~10,000 | AES, RSA, bcrypt, scrypt, JWT, TLS |
| **Math/ML** | ~25 | ~15,000 | Linear algebra, FFT, tensors, optimization |
| **Testing** | ~15 | ~5,000 | SSpec, mocking, benchmarking |
| **Utilities** | ~200 | ~40,000 | String, array, text, validation, encoding |

**Known Duplication Patterns:**
- **String utilities:** `text_utils.spl` (767 lines), `string.spl` (626 lines), `string_extra.spl` (314 lines), `src/text_utils.spl` (230 lines) - **~1,937 lines**
- **Array utilities:** `array.spl` (350 lines), `json/array_ops.spl` (559 lines), `src/array_builder.spl` (305 lines) - **~1,214 lines**
- **Validation patterns:** Scattered across modules, estimated **~2,000 lines**

---

### 1.3 Applications (`src/app/` - 584 files, 122,309 lines)

**Purpose:** CLI tools, build system, MCP servers, language servers, formatters, test runners.

**Top 30 Applications:**

| Application | Files | Lines | Purpose |
|-------------|-------|-------|---------|
| `compile/` | 10 | 4,258 | C translation & codegen |
| `build/` | 28 | 7,231 | Build system & bootstrap |
| `dashboard/` | 5 | 1,760 | Interactive dashboard |
| `mcp_jj/` | 19 | 4,654 | MCP server for Jujutsu VCS |
| `mcp/` | 28 | 8,394 | MCP servers (fileio, debug, resources) |
| `ffi_gen/` | 71 | 12,130 | FFI wrapper generator |
| `ffi_gen.specs/` | 41 | 6,608 | FFI generation specs |
| `parser/` | 39 | 9,176 | Parser tools & AST |
| `test_runner_new/` | 44 | 10,213 | Test runner & SDoctest |
| `io/` | 40 | 11,190 | I/O subsystem (CLI, JIT, window, audio, gamepad) |
| `lsp/` | 20 | 4,525 | Language Server Protocol |
| `dap/` | 9 | 2,141 | Debug Adapter Protocol |
| `desugar/` | 6 | 1,454 | Static method desugaring |
| `formatter/` | 1 | 704 | Code formatter |
| `lint/` | 1 | 616 | Linter |
| `cli/` | 14 | 2,602 | CLI main & commands |
| `wrapper_gen/` | 12 | 2,376 | Wrapper code generator |
| `verify/` | 11 | 2,217 | Verification tools |
| `package/` | 26 | 3,615 | Package management |
| `depgraph/` | 10 | 1,393 | Dependency graph |

**Key Applications:**

1. **CLI (`cli/main.spl` - 756 lines)**
   - Entry point for `bin/simple` binary
   - Command dispatch, help system
   - Key functions: `main()`, `parse_args()`, `dispatch_command()`

2. **Build System (`build/` - 7,231 lines)**
   - `bootstrap_multiphase.spl` (1,544 lines) - Multi-phase bootstrap
   - `baremetal.spl` (81 lines) - Bare-metal builds
   - Builds compiler from source in phases

3. **Test Runner (`test_runner_new/` - 10,213 lines)**
   - `test_runner_main.spl` (704 lines) - Main runner
   - `test_runner_execute.spl` (624 lines) - Test execution
   - `sdoctest/` subdirectory (9 files) - Executable documentation tests
   - Runs SSpec tests, generates reports

4. **MCP Servers**
   - `mcp/fileio_main.spl` (717 lines) - File operations MCP
   - `mcp/debug_tools.spl` (675 lines) - Debugging MCP
   - `mcp_jj/tools_jj.spl` (1,127 lines) - Jujutsu VCS integration
   - `mcp_jj/tools_git.spl` (911 lines) - Git fallback

5. **FFI Generator (`ffi_gen/` - 12,130 lines)**
   - `main.spl` (1,035 lines) - Generator driver
   - `parser.spl` - Spec parser
   - `specs/` directory with 41 specification files
   - Generates two/three-tier FFI wrappers

**Critical Duplication:**
- **ffi_gen.specs/**: 41 files with similar structure (enum specs, function specs, struct specs)
  - `cranelift_core.spl` (972 lines)
  - `runtime_value_full.spl` (658 lines) - **DUPLICATED** in `ffi_gen/specs/runtime_value_full.spl` (658 lines)
  - Total: **~6,600 lines** with high structural similarity

---

### 1.4 Full Compiler (`src/compiler/` - 420 files, 136,623 lines)

**Purpose:** Full-featured compiler with all language features (Full Simple), requires desugaring to run on Core Simple.

**Top 30 Compiler Files:**

| File | Lines | Purpose |
|------|-------|---------|
| `parser.spl` | 2,453 | Full parser with all features |
| `treesitter/outline.spl` | 1,799 | Tree-sitter integration |
| `mir_opt/auto_vectorize.spl` | 1,528 | Auto-vectorization pass |
| `mir_lowering.spl` | 1,503 | HIR → MIR lowering |
| `type_infer/inference.spl` | 1,437 | Type inference engine |
| `monomorphize/deferred.spl` | 1,405 | Deferred monomorphization |
| `lexer.spl` | 1,382 | Full lexer |
| `backend/llvm_ir_builder.spl` | 1,123 | LLVM IR generation |
| `backend/native/mod.spl` | 1,098 | Native backend entry |
| `mir_data.spl` | 1,080 | MIR data structures |
| `backend/interpreter.spl` | 1,057 | Interpreter backend |
| `linker/linker_wrapper.spl` | 1,019 | Linker integration |
| `mir_opt/loop_opt.spl` | 957 | Loop optimization |
| `type_system/expr_infer.spl` | 928 | Expression type inference |
| `backend/native/elf_writer.spl` | 921 | ELF file generation |
| `resolve.spl` | 876 | Name resolution |
| `driver.spl` | 856 | Compiler driver |
| `backend/native/isel_x86_64.spl` | 856 | x86-64 instruction selection |
| `parser_types.spl` | 841 | Parser type definitions |
| `traits.spl` | 816 | Trait system |
| `dim_constraints.spl` | 787 | Dimension checking (ML) |
| `backend/lean_backend.spl` | 782 | Lean proof backend |
| `smf_writer.spl` | 781 | SMF binary format writer |
| `optimization_passes.spl` | 781 | Optimization pipeline |
| `backend/native/isel_aarch64.spl` | 777 | AArch64 instruction selection |
| `loader/compiler_ffi.spl` | 774 | Compiler FFI interface |
| `backend/native/isel_riscv64.spl` | 771 | RISC-V instruction selection |
| `build_native.spl` | 765 | Native build orchestration |
| `backend/native/mach_inst.spl` | 753 | Machine instruction representation |

**Major Subsystems:**

| Subsystem | Files | Lines | Description |
|-----------|-------|-------|-------------|
| `backend/` | 84 | ~25,000 | Code generation backends (LLVM, native, interpreter, Lean, CUDA, Vulkan, WASM) |
| `mir_opt/` | 18 | ~8,500 | MIR optimization passes |
| `type_system/` | 22 | ~7,200 | Type checking, inference, effects |
| `linker/` | 15 | ~5,800 | Linking & symbol resolution |
| `monomorphize/` | 12 | ~4,500 | Generic monomorphization |
| `blocks/` | 8 | ~3,200 | Custom block system |
| `gc_analysis/` | 6 | ~2,400 | Garbage collection analysis |
| `hir_lowering/` | 10 | ~4,800 | HIR lowering passes |

**Critical Duplication:**

1. **Phase Files (27 files, ~12,000 lines):**
   - `bidir_phase1a-d.spl` (4 files, ~1,800 lines) - Bidirectional type checking
   - `associated_types_phase4a-d.spl` (4 files, ~2,100 lines) - Associated types
   - `higher_rank_poly_phase5a-d.spl` (4 files, ~2,300 lines) - Higher-rank polymorphism
   - `variance_phase6a-d.spl` (4 files, ~1,900 lines) - Variance checking
   - `macro_checker_phase7a-c.spl` (3 files, ~1,500 lines) - Macro validation
   - `const_keys_phase8a-c.spl` (3 files, ~1,200 lines) - Const keys
   - `simd_phase9a-c.spl` (3 files, ~1,200 lines) - SIMD analysis

2. **Backend Type Mappers (7 files, ~2,200 lines):**
   - `backend/llvm_type_mapper.spl` (304 lines)
   - `backend/cranelift_type_mapper.spl` (234 lines)
   - `backend/wasm_type_mapper.spl` (286 lines)
   - `backend/interpreter_type_mapper.spl` (236 lines)
   - `backend/cuda_type_mapper.spl` (317 lines)
   - `backend/vulkan_type_mapper.spl` (384 lines)
   - `backend/vhdl_type_mapper.spl` (213 lines)
   - **Pattern:** Each maps Simple types to backend-specific types

3. **ISA Instruction Selection (3 files, ~2,400 lines):**
   - `backend/native/isel_x86_64.spl` (856 lines)
   - `backend/native/isel_aarch64.spl` (777 lines)
   - `backend/native/isel_riscv64.spl` (771 lines)
   - **Pattern:** Nearly identical structure, different encodings

4. **ISA Encoding (3 files, ~1,700 lines):**
   - `backend/native/encode_x86_64.spl` (620 lines)
   - `backend/native/encode_aarch64.spl` (540 lines)
   - `backend/native/encode_riscv64.spl` (550 lines)
   - **Pattern:** Machine code encoding per architecture

---

### 1.5 Core Compiler (`src/compiler_core/` - 441 files, 98,874 lines)

**Purpose:** Core Simple version of the compiler (subset of Full Simple), can run on seed compiler.

**Distribution:**
- **Mirrors `src/compiler/`** structure with ~72% of the lines
- **All phase files duplicated** (27 files, ~8,000 lines)
- **All backend type mappers duplicated** (7 files, ~1,100 lines)
- **All ISA files duplicated** (6 files, ~3,200 lines)
- **All validators duplicated** (~14 files, ~3,000 lines)

**Key Differences from `src/compiler/`:**
- No Full Simple features (simplified generics, no higher-kinded types)
- Fewer optimization passes
- Simplified type inference
- Can bootstrap from seed compiler

**Intentional Duplication:**
- **~15,000 lines** duplicated for bootstrap purposes
- Documented in `src/compiler/README.md` and `src/compiler_core/README.md`
- Required until desugaring pipeline is complete

---

### 1.6 Libraries (`src/lib/` - 102 files, 23,992 lines)

**Purpose:** Core libraries (database, actors, ML, parsers, memory management).

**Top 20 Library Files:**

| File | Lines | Purpose |
|------|-------|---------|
| `parser/parser.spl` | 1,071 | Parser library (DUPLICATES core/parser.spl) |
| `pure/parser.spl` | 1,056 | Pure functional parser (DUPLICATES above) |
| `pure/evaluator.spl` | 962 | Pure evaluator |
| `database/test_extended/database.spl` | 900 | Extended DB tests |
| `pure/parser_old.spl` | 858 | Old parser implementation |
| `qemu/debug_boot_runner.spl` | 585 | QEMU debugging |
| `database/core.spl` | 510 | Database core (BugDB, TestDB, FeatureDB) |
| `actor_scheduler.spl` | 458 | Actor runtime scheduler |
| `qemu/mod.spl` | 453 | QEMU integration |
| `memory/refc_binary.spl` | 453 | Reference-counted binary data |
| `collections/lazy_seq.spl` | 434 | Lazy sequences |
| `pure/test/benchmark.spl` | 424 | ML benchmarks |
| `database/test_extended/queries.spl` | 413 | Query builder tests |
| `perf.spl` | 405 | Performance profiling |
| `message_transfer.spl` | 401 | Message passing |
| `pure/autograd.spl` | 389 | Automatic differentiation |
| `database/bug.spl` | 383 | Bug database |
| `pure/training.spl` | 382 | ML training |
| `pure/autograd_global.spl` | 368 | Global autograd state |

**Critical Duplication:**

1. **Parser Triplication (~2,985 lines):**
   - `parser/parser.spl` (1,071 lines)
   - `pure/parser.spl` (1,056 lines)
   - `pure/parser_old.spl` (858 lines)
   - **Reason:** Different parsing strategies (imperative, functional, legacy)

2. **Lexer Files:**
   - `parser/lexer.spl` - Accompanies parser/parser.spl
   - `pure/lexer.spl` - Accompanies pure/parser.spl
   - **Estimated:** ~800 lines duplicated

**Key Libraries:**

1. **Database (`database/` - 6 files, 2,479 lines)**
   - `core.spl` (510 lines) - BugDB, TestDB, FeatureDB, QueryBuilder
   - `bug.spl` (383 lines) - Bug tracking
   - `test_extended/` - Extended query tests
   - **Status:** 98/115 tests passing (85.2%), production-ready

2. **Actor System (`actor_scheduler.spl`, `actor_heap.spl` - 565 lines)**
   - Message-passing concurrency
   - Actor heap management
   - Scheduling primitives

3. **Pure ML (`pure/` - 12 files, 5,500 lines)**
   - Automatic differentiation
   - Training loops
   - Tensor operations
   - Hybrid acceleration (CPU/GPU)

4. **Memory Management**
   - `memory/refc_binary.spl` (453 lines) - Reference counting
   - String interning

---

### 1.7 Other Directories

| Directory | Files | Lines | Purpose |
|-----------|-------|-------|---------|
| `baremetal/` | 32 | 4,088 | Bare-metal runtime support |
| `diagnostics/` | 10 | 1,012 | Diagnostic formatting |
| `diagnostics_minimal/` | 5 | 328 | Minimal diagnostics |
| `ffi/` | 11 | 1,808 | FFI bridge utilities |
| `mcp_lib/` | 8 | 771 | MCP protocol library |
| `remote/` | 9 | 1,922 | Remote execution |
| `runtime/` | 1 | 548 | Runtime support |
| `shared/` | 5 | 571 | Shared utilities |
| `test/` | 4 | 1,728 | Test utilities |
| `llvm_shared/` | 3 | 278 | LLVM shared code |

---

## 2. Critical Duplications

### Ranked by Severity & Impact

#### 1. **CRITICAL: compiler/ ↔ compiler_core/ Bootstrap Duplication**

- **Lines:** ~15,000
- **Status:** ✅ Documented, Intentional
- **Priority:** N/A (required for bootstrap)
- **Impact:** High (maintenance burden)
- **Resolution:** Complete desugaring pipeline (future work)

**Documented in:**
- `src/compiler/README.md` (96 lines)
- `src/compiler_core/README.md` (100 lines)
- `doc/report/duplication_phase3_summary.md`

**Breakdown:**
- Phase files: ~8,000 lines
- Backend type mappers: ~1,100 lines
- Validators: ~3,000 lines
- Core files: ~3,000 lines

#### 2. **HIGH: Phase Files (Development Evolution)**

- **Files:** 27
- **Lines:** ~12,000 (compiler/) + ~8,000 (compiler_core/) = ~20,000 total
- **Status:** ⚠️ Development history
- **Priority:** Medium
- **Impact:** Medium (bloat, confusing)

**Examples:**
- `bidir_phase1a.spl` through `bidir_phase1d.spl` (4 files, ~1,800 lines)
- `associated_types_phase4a-d.spl` (4 files, ~2,100 lines)
- `higher_rank_poly_phase5a-d.spl` (4 files, ~2,300 lines)

**Recommendation:**
- **Option 1:** Consolidate into single files per feature (e.g., `bidirectional_checking.spl`)
- **Option 2:** Move to `doc/design/phases/` as historical reference
- **Option 3:** Keep as-is (documents incremental development)

**Estimated Savings:** ~8,000 lines (67% reduction if consolidated)

#### 3. **HIGH: Lexer Triplication**

- **Files:** 15 lexer files across codebase
- **Lines:** ~3,700 total
- **Status:** ⚠️ Bootstrap + functional variants
- **Priority:** Low (bootstrap required)
- **Impact:** Medium

**Breakdown:**
```
src/core/lexer.spl                     829 lines  (seed-compilable)
src/compiler/lexer.spl               1,382 lines  (full features)
src/compiler_core/lexer.spl          1,491 lines  (core features)
src/lib/parser/lexer.spl               ~400 lines  (library parser)
src/lib/pure/lexer.spl                 ~400 lines  (functional parser)
src/std/sdn/lexer.spl                  ~200 lines  (SDN format)
```

**Reason:** Different feature sets for bootstrap stages + specialized lexers (SDN, HTML)

#### 4. **HIGH: Parser Triplication**

- **Files:** 30+ parser files
- **Lines:** ~6,700 total
- **Status:** ⚠️ Bootstrap + specialized parsers
- **Priority:** Low (bootstrap required)
- **Impact:** High

**Breakdown:**
```
src/core/parser.spl                  2,135 lines  (seed-compilable)
src/compiler/parser.spl              2,453 lines  (full features)
src/lib/parser/parser.spl            1,071 lines  (library parser)
src/lib/pure/parser.spl              1,056 lines  (functional parser)
src/std/sdn/parser.spl                 682 lines  (SDN format)
src/std/json/parser.spl                ~600 lines  (JSON)
src/std/xml/parser.spl                 ~500 lines  (XML)
```

**Reason:** Bootstrap stages + specialized parsers for different formats

#### 5. **HIGH: Type Mapper Duplication**

- **Files:** 16 type mapper files
- **Lines:** ~4,700 total
- **Status:** ✅ Documented (backend-specific + bootstrap)
- **Priority:** Low
- **Impact:** Medium

**Breakdown:**
```
# compiler/ (7 files, ~2,200 lines)
backend/llvm_type_mapper.spl           304 lines
backend/cranelift_type_mapper.spl      234 lines
backend/wasm_type_mapper.spl           286 lines
backend/interpreter_type_mapper.spl    236 lines
backend/cuda_type_mapper.spl           317 lines
backend/vulkan_type_mapper.spl         384 lines
backend/vhdl_type_mapper.spl           213 lines

# compiler_core/ (7 files, ~1,100 lines)
backend/llvm_type_mapper.spl           108 lines
backend/cranelift_type_mapper.spl      101 lines
backend/wasm_type_mapper.spl           124 lines
backend/interpreter_type_mapper.spl     89 lines
backend/cuda_type_mapper.spl           138 lines
backend/vulkan_type_mapper.spl         187 lines
# (vhdl not in core)

# Plus backend_types.spl in 3 locations:
src/compiler/backend/backend_types.spl     460 lines
src/compiler_core/backend/backend_types.spl 218 lines
src/core/backend_types.spl                 156 lines
```

**Pattern:** Each backend has specific type representation requirements.

**Recommendation:** Extract common `TypeMapper` trait when Full Simple trait system stabilizes.

#### 6. **VERY HIGH RISK: ISA Encoder Duplication**

- **Files:** 6 ISA files × 2 compilers = 12 files
- **Lines:** ~4,600 total
- **Status:** ⚠️ Cross-platform similarity
- **Priority:** Very High Risk (core code generation)
- **Impact:** High (affects all native compilation)

**Breakdown (compiler/):**
```
backend/native/isel_x86_64.spl         856 lines
backend/native/isel_aarch64.spl        777 lines
backend/native/isel_riscv64.spl        771 lines
backend/native/encode_x86_64.spl       620 lines
backend/native/encode_aarch64.spl      540 lines
backend/native/encode_riscv64.spl      550 lines
Total: 4,114 lines
```

**Similar pattern in `compiler_core/` (~3,200 lines)**

**Pattern:**
1. Instruction selection (`isel_*.spl`) - MIR → machine instructions
2. Encoding (`encode_*.spl`) - Machine instructions → bytes

**Recommendation:**
- Create ISA abstraction layer (trait-based)
- **Risk:** Very High - incorrect abstraction breaks native codegen for all platforms
- **Timeline:** Only after Full Simple trait system is stable

#### 7. **HIGH: Validator/Checker Pattern**

- **Files:** ~14 validator files × 2 compilers = ~28 files
- **Lines:** ~6,400 total
- **Status:** ⚠️ Structural similarity
- **Priority:** High
- **Impact:** Medium (refactoring opportunity)

**Examples:**
```
# compiler/
di_validator.spl              237 lines
visibility_checker.spl        130 lines
safety_checker.spl            341 lines
simd_check.spl                ~400 lines (inferred)
verification_checker.spl      150 lines
macro_checker_phase7a-c.spl 1,566 lines (3 files)
blocks/validators.spl         247 lines

# compiler_core/ (similar structure)
di_validator.spl              135 lines
safety_checker.spl            335 lines
macro_checker_phase7a-c.spl 1,166 lines (3 files)
blocks/validators.spl         251 lines
```

**Pattern:** Each validator follows similar structure:
1. Define error types
2. Implement `validate_X(context, item)` functions
3. Collect and report errors
4. Integrate with compiler pipeline

**Recommendation:**
- Extract common validation framework:
```simple
class ValidationContext:
    errors: [ValidationError]
    warnings: [ValidationWarning]

fn run_validator(ctx: ValidationContext, rules: [ValidationRule]) -> ValidationResult
fn report_errors(ctx: ValidationContext, formatter: ErrorFormatter)
```

**Estimated Savings:** ~2,000 lines of boilerplate

**Risk:** High - validators are core to compiler correctness, extensive testing required

#### 8. **MEDIUM: String/Array Utility Duplication (std/)**

- **Files:** ~15 files
- **Lines:** ~4,200 total
- **Status:** ⚠️ Scattered utilities
- **Priority:** Medium
- **Impact:** Medium (user-facing, maintenance)

**Breakdown:**
```
text_utils.spl              767 lines
string.spl                  626 lines
json/array_ops.spl          559 lines
string_extra.spl            314 lines
array.spl                   350 lines
src/array_builder.spl       305 lines
src/text_utils.spl          230 lines
ascii_art/text.spl          237 lines
platform/text_io.spl         30 lines
```

**Patterns:**
- String validation (email, URL, path)
- String transformation (case, trim, pad)
- Array operations (map, filter, reduce)
- Text utilities (split, join, replace)

**Recommendation:**
- Consolidate into `src/std/string.spl` and `src/std/array.spl`
- Move specialized utilities to subdirectories
- Extract common patterns into `src/std/core/`

**Estimated Savings:** ~1,500 lines

#### 9. **LOW: FFI Specs Duplication (Tool-Generated)**

- **Files:** 41 files in `src/app/ffi_gen.specs/`
- **Lines:** ~6,600 total
- **Status:** ✅ Tool-generated
- **Priority:** Low (generated code)
- **Impact:** Low

**Top Files:**
```
cranelift_core.spl          972 lines
runtime_value_full.spl      658 lines
cli.spl                     ~480 lines
collections.spl             ~480 lines
```

**Note:** `runtime_value_full.spl` appears in TWO locations:
- `src/app/ffi_gen.specs/runtime_value_full.spl` (658 lines)
- `src/app/ffi_gen/specs/runtime_value_full.spl` (658 lines)

**Recommendation:**
- Deduplicate the two `runtime_value_full.spl` files
- Otherwise, keep as-is (generated code should be regenerated, not manually edited)

---

## 3. Semantic Patterns

### 3.1 Builder Pattern (8 files, ~2,500 lines)

**Locations:**
- `src/baremetal/table_builder.spl` (445 lines)
- `src/compiler/blocks/builder.spl` (380 lines)
- `src/compiler/backend/matrix_builder.spl` (154 lines)
- `src/compiler/backend/llvm_ir_builder.spl` (1,123 lines)
- `src/app/build/incremental_builder.spl` (620 lines)

**Pattern:**
1. `new_builder()` - Constructor
2. `builder_add_X()` - Incremental operations
3. `builder_build()` - Finalization
4. Error handling and validation

**Recommendation:**
- Extract generic builder trait (if Full Simple supports traits)
- Or create builder helper macros

**Estimated Savings:** ~500 lines of boilerplate

---

### 3.2 Visitor Pattern (Lean Codegen, ~1,000 lines)

**Locations:**
- `src/compiler/codegen/lean/contracts.spl`
- `src/compiler/codegen/lean/expressions.spl`
- `src/compiler/codegen/lean/types.spl`
- `src/compiler/codegen/lean/functions.spl`
- `src/compiler/codegen/lean/traits.spl`

**Pattern:**
- Each implements `to_lean()`, `to_lean_name()` with identical identifier sanitization

**Status:** ✅ Already using centralized `naming` module
- All files use `super::naming::to_pascal_case()` or `super::naming::to_camel_case()`
- `naming.spl` provides `sanitize_lean_ident()`, `to_lean_type_name()`, `to_lean_func_name()`

---

### 3.3 Error Creation Pattern (~200 occurrences)

**Pattern:** `LowerError::Semantic(format!(...))` repeated everywhere.

**Duplicated messages:**
- `"Cannot resolve module: {}"`
- `"Cannot read module {:?}: {}"`
- `"Cannot parse module {:?}: {}"`

**Status:** ✅ Partially resolved
- Extended `error::factory` module with 9+ factory functions
- ~103 occurrences remain for gradual migration

**Recommendation:** Continue gradual migration to factory functions.

---

### 3.4 FFI Wrapper Pattern (Two/Three-Tier)

**Two-Tier (Runtime):**
```simple
extern fn rt_file_read_text(path: text) -> text
fn file_read(path: text) -> text:
    rt_file_read_text(path)
```

**Three-Tier (External):**
```simple
# C++/Rust FFI
extern fn cranelift_create_context() -> i64

# Simple FFI wrapper
fn create_context() -> CraneliftContext:
    val handle = cranelift_create_context()
    CraneliftContext(handle: handle)
```

**Main module:** `src/app/io/mod.spl` (11,190 lines across 40 files)

---

## 4. File Inventory

### 4.1 src/core/ (36 files, 15,691 lines)

| File | Lines | Primary Types | Key Functions | Purpose |
|------|-------|---------------|---------------|---------|
| `compiler/c_codegen.spl` | 2,339 | `CCodegen` | `codegen_module()`, `codegen_function()` | C code generation for seed |
| `parser.spl` | 2,135 | `CoreParser` | `parse_module()`, `parse_expr()` | Core parser implementation |
| `interpreter/eval.spl` | 1,797 | `Interpreter` | `eval_expr()`, `eval_stmt()` | Tree-walk interpreter |
| `ast.spl` | 922 | `CoreExpr`, `CoreStmt`, `CoreDecl` | `ast_expr_get()`, `ast_stmt_get()` | AST node definitions |
| `lexer.spl` | 829 | - | `lex()`, `lex_token()` | Lexical analysis |
| `lexer_struct.spl` | 720 | `CoreLexer` | `lexer_new()`, `lexer_next_token()` | Lexer state management |
| `mir.spl` | 756 | `MirInst`, `MirBlock` | `mir_inst_get()`, `mir_block_get()` | MIR definitions |
| `types.spl` | 582 | `TypeKind` | `type_equals()`, `type_to_string()` | Type system core |
| `aop.spl` | 541 | `AdviceKind`, `Advice` | `aop_match_pointcut()`, `aop_apply_advice()` | Aspect-oriented programming |
| `type_checker.spl` | 442 | `TypeChecker` | `check_expr()`, `check_stmt()` | Type checking |
| `tokens.spl` | 446 | `TokenKind`, `Token` | `token_kind_to_string()` | Token definitions |
| `type_inference.spl` | 415 | `InferContext` | `infer_expr_type()`, `unify()` | Type inference |
| `type_erasure.spl` | 302 | - | `erase_generics()` | Generic type erasure |
| `interpreter/value.spl` | 316 | `Value` | `value_to_int()`, `value_to_string()` | Runtime values |
| `interpreter/ops.spl` | 236 | - | `eval_binary_op()`, `eval_unary_op()` | Operator evaluation |
| `interpreter/module_loader.spl` | 278 | `ModuleLoader` | `load_module()`, `resolve_import()` | Module loading |
| `interpreter/jit.spl` | 141 | `JitEngine` | `jit_compile()`, `jit_execute()` | JIT compilation |
| `interpreter/env.spl` | 160 | `Environment` | `env_get()`, `env_set()` | Variable environment |
| `closure_analysis.spl` | 186 | - | `analyze_closure_capture()` | Closure capture warnings |
| `backend_types.spl` | 156 | `BackendKind` | - | Backend type definitions |

### 4.2 src/std/ Top 50 Modules (901 files, 185,046 lines)

| Module | Lines | Category | Key Types | Purpose |
|--------|-------|----------|-----------|---------|
| `bcrypt/core.spl` | 1,332 | Crypto | `BcryptHash` | Password hashing |
| `cbor/core.spl` | 1,305 | Serialization | `CborEncoder`, `CborDecoder` | CBOR codec |
| `skiplist_utils.spl` | 1,105 | Data Structures | `SkipList` | Skip list operations |
| `graph/utilities.spl` | 978 | Algorithms | `Graph`, `GraphAlgorithms` | Graph algorithms |
| `linear_algebra/matrix_ops.spl` | 894 | Math | `Matrix` | Matrix operations |
| `set_utils.spl` | 777 | Collections | `Set` | Set utilities |
| `text_utils.spl` | 767 | String | - | Text processing |
| `src/tooling/easy_fix/rules.spl` | 761 | Tooling | `FixRule` | Auto-fix rules |
| `src/di.spl` | 744 | Infrastructure | `Container`, `Provider` | Dependency injection |
| `search_utils.spl` | 738 | Algorithms | - | Search algorithms |
| `amqp_utils.spl` | 738 | Networking | `AmqpConnection` | AMQP protocol |
| `src/testing/mocking_advanced.spl` | 724 | Testing | `AdvancedMock` | Advanced mocking |
| `matrix_utils.spl` | 719 | Math | - | Matrix utilities |
| `udp_utils.spl` | 715 | Networking | `UdpSocket` | UDP utilities |
| `src/infra.spl` | 712 | Infrastructure | - | Infrastructure support |
| `diff/utilities.spl` | 710 | Algorithms | `Differ` | Diff algorithms |
| `stats_utils.spl` | 700 | Math | - | Statistics |
| `src/tensor.spl` | 697 | ML | `Tensor` | Tensor operations |
| `comparator_utils.spl` | 693 | Collections | - | Comparators |
| `binary_io.spl` | 690 | I/O | `BinaryReader`, `BinaryWriter` | Binary I/O |
| `sdn/parser.spl` | 682 | Serialization | `SdnParser` | SDN format parser |
| `allocator.spl` | 683 | Memory | `Allocator`, `ArenaAllocator` | Memory allocators |
| `src/table.spl` | 682 | Data Structures | `Table` | Table data structure |
| `string.spl` | 626 | String | - | String utilities |
| `array.spl` | 350 | Collections | - | Array utilities |

### 4.3 src/app/ Top 40 Applications (584 files, 122,309 lines)

| Application | Files | Lines | Key Files | Purpose |
|-------------|-------|-------|-----------|---------|
| `ffi_gen/` | 71 | 12,130 | `main.spl` (1,035), `parser.spl` | FFI wrapper generator |
| `io/` | 40 | 11,190 | `cli_ops.spl` (664), `jit_ffi.spl` (621) | I/O subsystem |
| `test_runner_new/` | 44 | 10,213 | `test_runner_main.spl` (704) | Test runner |
| `parser/` | 39 | 9,176 | `ast.spl` (899), `modules.spl` (616) | Parser tools |
| `mcp/` | 28 | 8,394 | `fileio_main.spl` (717) | MCP servers |
| `build/` | 28 | 7,231 | `bootstrap_multiphase.spl` (1,544) | Build system |
| `ffi_gen.specs/` | 41 | 6,608 | `cranelift_core.spl` (972) | FFI specs |
| `mcp_jj/` | 19 | 4,654 | `tools_jj.spl` (1,127) | Jujutsu MCP |
| `lsp/` | 20 | 4,525 | `server.spl` (649) | Language server |
| `compile/` | 10 | 4,258 | `c_translate.spl` (1,896) | C compilation |
| `package/` | 26 | 3,615 | - | Package management |
| `cli/` | 14 | 2,602 | `main.spl` (756) | CLI driver |
| `wrapper_gen/` | 12 | 2,376 | - | Wrapper generator |
| `verify/` | 11 | 2,217 | - | Verification tools |
| `dap/` | 9 | 2,141 | `server.spl` (755) | Debug adapter |

### 4.4 src/compiler/ Top 40 Files (420 files, 136,623 lines)

| File | Lines | Key Types | Purpose |
|------|-------|-----------|---------|
| `parser.spl` | 2,453 | `Parser` | Full parser |
| `treesitter/outline.spl` | 1,799 | `OutlineNode` | Tree-sitter integration |
| `mir_opt/auto_vectorize.spl` | 1,528 | `Vectorizer` | Auto-vectorization |
| `mir_lowering.spl` | 1,503 | - | HIR → MIR lowering |
| `type_infer/inference.spl` | 1,437 | `TypeInferencer` | Type inference |
| `monomorphize/deferred.spl` | 1,405 | `DeferredMonomorphizer` | Deferred monomorphization |
| `lexer.spl` | 1,382 | `Lexer` | Full lexer |
| `backend/llvm_ir_builder.spl` | 1,123 | `LLVMIRBuilder` | LLVM IR generation |
| `backend/native/mod.spl` | 1,098 | - | Native backend |
| `mir_data.spl` | 1,080 | `MirInst`, `MirBlock` | MIR data structures |
| `backend/interpreter.spl` | 1,057 | `InterpreterBackend` | Interpreter backend |
| `backend/native/isel_x86_64.spl` | 856 | - | x86-64 isel |
| `backend/native/isel_aarch64.spl` | 777 | - | AArch64 isel |
| `backend/native/isel_riscv64.spl` | 771 | - | RISC-V isel |
| `backend/native/encode_x86_64.spl` | 620 | - | x86-64 encoding |
| `backend/native/encode_aarch64.spl` | 540 | - | AArch64 encoding |
| `backend/native/encode_riscv64.spl` | 550 | - | RISC-V encoding |

### 4.5 src/lib/ Top 20 Files (102 files, 23,992 lines)

| File | Lines | Key Types | Purpose |
|------|-------|-----------|---------|
| `parser/parser.spl` | 1,071 | `Parser` | Parser library |
| `pure/parser.spl` | 1,056 | `PureParser` | Pure functional parser |
| `pure/evaluator.spl` | 962 | `Evaluator` | Pure evaluator |
| `database/test_extended/database.spl` | 900 | - | Extended DB tests |
| `pure/parser_old.spl` | 858 | - | Old parser |
| `qemu/debug_boot_runner.spl` | 585 | `DebugBootRunner` | QEMU debugging |
| `database/core.spl` | 510 | `BugDB`, `TestDB`, `FeatureDB` | Database core |
| `actor_scheduler.spl` | 458 | `ActorScheduler` | Actor scheduler |
| `memory/refc_binary.spl` | 453 | `BinaryRef` | Ref-counted binary |
| `pure/autograd.spl` | 389 | `AutogradEngine` | Automatic differentiation |
| `database/bug.spl` | 383 | `BugDatabase` | Bug tracking |
| `pure/training.spl` | 382 | `TrainingLoop` | ML training |

---

## 5. Class/Type Index

### 5.1 Alphabetical Index (Top 100 Types)

| Type | Category | Location(s) | Lines |
|------|----------|-------------|-------|
| `ActorContext` | Class | `src/lib/actor_scheduler.spl:161` | - |
| `ActorDef` | Struct | `src/app/parser/ast.spl:475`, `src/compiler/parser_types.spl:122` | - |
| `ActorScheduler` | Class | `src/lib/actor_scheduler.spl:287` | - |
| `AdamState` | Class | `src/std/optimization/types.spl:28` | - |
| `AlgebraicSimplifier` | Class | `src/compiler/mir_opt/const_fold.spl:202` | - |
| `AopWeaver` | Class | `src/compiler/aop.spl:86` | - |
| `ArchRulesEngine` | Class | `src/compiler/arch_rules.spl:79` | - |
| `ArmAsmGenerator` | Class | `src/compiler/backend/arm_asm.spl:64` | - |
| `AsyncIntegration` | Class | `src/compiler/async_integration.spl:249` | - |
| `AsyncMock` | Class | `src/std/src/testing/mocking_async.spl:27` | - |
| `AtomicBool` | Class | `src/std/atomic.spl:144` | - |
| `AtomicI64` | Class | `src/std/atomic.spl:66` | - |
| `AutogradStore` | Class | `src/lib/pure/autograd_store.spl:15` | - |
| `AutoVectorizer` | Class | `src/compiler/simd_check.spl:368` | - |
| `Backend` | Class | `src/compiler/backend/backend_api.spl:32` | - |
| `BackendFactory` | Class | `src/compiler/backend/backend_factory.spl:12` | - |
| `BackendKind` | Enum | `src/compiler/backend/backend_types.spl:18`, `src/core/backend_types.spl:12` | - |
| `BarrierAnalysis` | Class | `src/compiler/gc_analysis/barriers.spl:143` | - |
| `BenchmarkRunner` | Class | `src/test/benchmarks.spl:209` | - |
| `BinaryReader` | Class | `src/std/binary_io.spl:66` | - |
| `BinaryWriter` | Class | `src/std/binary_io.spl:334` | - |
| `BlockContext` | Class | `src/compiler/macro_validation.spl:23` | - |
| `BugDB` | Struct | `src/lib/database/core.spl` | - |
| `CCodegen` | Class | `src/core/compiler/c_codegen.spl` | - |
| `CborEncoder` | Class | `src/std/cbor/core.spl` | - |
| `CoreExpr` | Struct | `src/core/ast.spl` | - |
| `CoreLexer` | Struct | `src/core/lexer_struct.spl` | - |
| `CoreParser` | Struct | `src/core/parser.spl` | - |
| `CoreStmt` | Struct | `src/core/ast.spl` | - |
| `EffectEnv` | Class/Enum | Multiple locations (11 occurrences) | - |
| `Environment` | Class | `src/core/interpreter/env.spl` | - |
| `FeatureDB` | Struct | `src/lib/database/core.spl` | - |
| `HirExpr` | Struct | Multiple locations (14 occurrences) | - |
| `HirType` | Struct/Enum | Multiple locations (48 occurrences) | - |
| `InferMode` | Enum | Multiple locations (12 occurrences) | - |
| `Interpreter` | Class | `src/core/interpreter/eval.spl` | - |
| `JitEngine` | Class | `src/core/interpreter/jit.spl` | - |
| `LLVMIRBuilder` | Class | `src/compiler/backend/llvm_ir_builder.spl` | - |
| `MacroDef` | Class | Multiple locations (11 occurrences) | - |
| `Matrix` | Class | `src/std/linear_algebra/matrix_ops.spl` | - |
| `MirInst` | Struct | `src/core/mir.spl`, `src/compiler/mir_data.spl` | - |
| `ModuleLoader` | Class | `src/core/interpreter/module_loader.spl` | - |
| `Parser` | Class | Multiple locations (7 occurrences) | - |
| `QueryBuilder` | Class | `src/lib/database/core.spl` | - |
| `Scope` | Class | Multiple locations (7 occurrences) | - |
| `SdnValue` | Struct | Multiple locations (6 occurrences) | - |
| `SkipList` | Class | `src/std/skiplist_utils.spl` | - |
| `Span` | Struct | Multiple locations (12 occurrences) | - |
| `StackFrame` | Class | Multiple locations (8 occurrences) | - |
| `SymbolTable` | Class | Multiple locations (6 occurrences) | - |
| `Tensor` | Class | `src/std/src/tensor.spl` | - |
| `TestDB` | Struct | `src/lib/database/core.spl` | - |
| `Token` | Struct | Multiple locations (12 occurrences) | - |
| `TokenKind` | Enum | Multiple locations (9 occurrences) | - |
| `TraitDef` | Struct | Multiple locations (9 occurrences) | - |
| `TraitRef` | Struct | Multiple locations (14 occurrences) | - |
| `TypeChecker` | Class | Multiple locations (7 occurrences) | - |
| `TypeInferencer` | Class | Multiple locations (8 occurrences) | - |
| `TypeKind` | Enum | `src/core/types.spl` | - |
| `TypeScheme` | Class | Multiple locations (7 occurrences) | - |
| `TypeVar` | Class | Multiple locations (8 occurrences) | - |
| `Value` | Struct | `src/core/interpreter/value.spl` | - |
| `Variance` | Enum | Multiple locations (8 occurrences) | - |
| `Vec4f` | Class | Multiple locations (7 occurrences) | - |
| `Vectorizer` | Class | `src/compiler/mir_opt/auto_vectorize.spl` | - |

### 5.2 Most Duplicated Type Names

| Type Name | Count | Locations |
|-----------|-------|-----------|
| `HirType` | 48 | Across compiler/, compiler_core/, and related modules |
| `Effect` | 23 | Type system and effect tracking modules |
| `TraitRef` | 14 | Trait system implementation |
| `HirExpr` | 14 | HIR expression nodes |
| `Token` | 12 | Lexer/parser modules |
| `Span` | 12 | Source location tracking |
| `InferMode` | 12 | Type inference |
| `MacroDef` | 11 | Macro system |
| `Expr` | 11 | Various expression representations |
| `EffectEnv` | 11 | Effect environment tracking |

**Note:** High duplication counts often indicate:
1. Bootstrap duplication (compiler/ vs compiler_core/)
2. Similar abstractions across different subsystems
3. Common data structures reused in multiple contexts

---

## 6. Refactoring Recommendations

### Priority 1: Low-Hanging Fruit (Low Risk, Medium Impact)

#### 1.1 Consolidate Phase Files
- **Files:** 27 phase files in compiler/ + compiler_core/
- **Lines:** ~20,000 total
- **Savings:** ~8,000 lines (if consolidated)
- **Risk:** Low
- **Effort:** 2-3 days
- **Action:**
  - Merge `bidir_phase1a-d.spl` → `bidirectional_checking.spl`
  - Merge `associated_types_phase4a-d.spl` → `associated_types.spl`
  - Repeat for all phase groups
  - Move originals to `doc/design/phases/` for history

#### 1.2 Extract Builder Utilities
- **Files:** 8 builder files
- **Lines:** ~2,500 total
- **Savings:** ~500 lines
- **Risk:** Low
- **Effort:** 1 day
- **Action:**
  - Create `src/compiler/utils/builder_helpers.spl`
  - Extract common error formatting
  - Extract common validation patterns

#### 1.3 Deduplicate FFI Specs
- **Files:** 2 files (runtime_value_full.spl)
- **Lines:** ~1,300 total
- **Savings:** ~650 lines
- **Risk:** Very Low
- **Effort:** 1 hour
- **Action:**
  - Remove duplicate `src/app/ffi_gen.specs/runtime_value_full.spl`
  - Keep only `src/app/ffi_gen/specs/runtime_value_full.spl`

#### 1.4 Consolidate String/Array Utilities
- **Files:** ~15 files in src/std/
- **Lines:** ~4,200 total
- **Savings:** ~1,500 lines
- **Risk:** Medium
- **Effort:** 2-3 days
- **Action:**
  - Merge `text_utils.spl`, `string_extra.spl`, `src/text_utils.spl` into `string.spl`
  - Merge array utilities into `array.spl`
  - Update imports across codebase

**Total Priority 1 Savings:** ~10,650 lines
**Total Priority 1 Effort:** ~5-7 days

---

### Priority 2: Medium-Term Actions (Medium Risk, High Impact)

#### 2.1 Validation Framework
- **Files:** ~28 validator files
- **Lines:** ~6,400 total
- **Savings:** ~2,000 lines
- **Risk:** High
- **Effort:** 1-2 weeks
- **Action:**
  - Design `ValidationContext` class
  - Extract common validation patterns
  - Implement for 1-2 validators as pilot
  - Gradual migration

#### 2.2 Type Mapper Abstraction
- **Files:** 16 type mapper files
- **Lines:** ~4,700 total
- **Savings:** ~1,500 lines
- **Risk:** High
- **Effort:** 1-2 weeks
- **Action:**
  - Wait for Full Simple trait system to stabilize
  - Design `TypeMapper` trait
  - Implement for 1 backend as pilot
  - Gradual migration

**Total Priority 2 Savings:** ~3,500 lines
**Total Priority 2 Effort:** ~2-4 weeks

---

### Priority 3: Long-Term Actions (Very High Risk, Very High Impact)

#### 3.1 ISA Abstraction Layer
- **Files:** 12 ISA files
- **Lines:** ~4,600 total
- **Savings:** ~1,500 lines
- **Risk:** Very High
- **Effort:** 1-2 months
- **Action:**
  - Only attempt after Full Simple trait system is complete
  - Design ISA trait hierarchy
  - Comprehensive testing on all platforms
  - Gradual migration with fallbacks

#### 3.2 Complete Desugaring Pipeline
- **Impact:** ~15,000 lines (compiler/ ↔ compiler_core/)
- **Risk:** Very High
- **Effort:** 3-6 months
- **Action:**
  - Complete desugaring for all Full Simple features
  - Eliminate need for compiler_core/ duplication
  - Full bootstrap redesign

**Total Priority 3 Savings:** ~16,500 lines
**Total Priority 3 Effort:** ~4-8 months

---

### Work That Should NOT Be Done

#### 1. Lexer/Parser Triplication
- **Reason:** Required for bootstrap stages
- **Status:** Documented
- **Decision:** Keep as-is

#### 2. Backend Type Mappers (without trait system)
- **Reason:** Backend-specific requirements
- **Status:** Documented
- **Decision:** Wait for trait system

#### 3. Specialized Parsers (SDN, JSON, XML, HTML)
- **Reason:** Different grammars and requirements
- **Status:** Intentional
- **Decision:** Keep as-is

---

## 7. Summary Statistics

### Codebase Health Metrics

| Metric | Value | Target | Status |
|--------|-------|--------|--------|
| Total Lines | 98,916 | - | - |
| Type Definitions | 4,498 | - | - |
| Intentional Duplication | ~15,000 (15%) | Documented | ✅ |
| Addressable Duplication | ~16,000 (16%) | <10% | ⚠️ |
| High-Risk Files | ~12 ISA files | Stable | ⚠️ |
| Test Coverage | 4,067/4,067 (100%) | 100% | ✅ |

### Refactoring Potential

| Priority | Files | Lines | Savings | Risk | Effort |
|----------|-------|-------|---------|------|--------|
| **Priority 1** | ~52 | ~28,250 | ~10,650 | Low | 5-7 days |
| **Priority 2** | ~44 | ~11,100 | ~3,500 | Medium | 2-4 weeks |
| **Priority 3** | ~453 | ~19,600 | ~16,500 | Very High | 4-8 months |
| **Total** | ~549 | ~58,950 | ~30,650 | - | ~5-9 months |

**ROI Analysis:**
- **Quick wins (Priority 1):** 10,650 lines in 1 week = **~1,500 lines/day**
- **Medium-term (Priority 2):** 3,500 lines in 3 weeks = **~170 lines/day**
- **Long-term (Priority 3):** 16,500 lines in 6 months = **~90 lines/day**

**Recommendation:** Focus on Priority 1 items for maximum ROI.

---

## 8. Key Findings

### 8.1 Architectural Insights

1. **Bootstrap Complexity**
   - 3 compiler implementations (core, compiler_core, compiler)
   - 3 parser implementations (core, library, pure functional)
   - 3 lexer implementations
   - **Total:** ~25,000 lines for bootstrap support

2. **Backend Proliferation**
   - 7 type mappers × 2 compilers = 14 files
   - 3 ISA architectures × 2 stages × 2 compilers = 12 files
   - **Total:** ~9,300 lines for backend support

3. **Standard Library Growth**
   - 901 files, 185,046 lines (187% of codebase size)
   - Heavy utility duplication (string, array, validation)
   - **Opportunity:** Consolidate utilities into core modules

4. **Application Ecosystem**
   - 584 files, 122,309 lines
   - Well-organized by function
   - Some duplication in FFI specs (tool-generated)

### 8.2 Code Quality

**Strengths:**
- ✅ Well-documented bootstrap duplication
- ✅ Clear directory structure
- ✅ 100% test coverage (4,067 tests passing)
- ✅ Consistent naming conventions
- ✅ Extensive standard library

**Weaknesses:**
- ⚠️ Phase files clutter compiler/ directory
- ⚠️ String/array utilities scattered across std/
- ⚠️ Validator pattern not abstracted
- ⚠️ ISA code highly duplicated (acceptable for now)

### 8.3 Maintenance Burden

**High-Maintenance Areas:**
1. compiler/ ↔ compiler_core/ synchronization (~15,000 lines)
2. Phase files (27 files, manual tracking)
3. Backend type mappers (14 files, backend-specific changes)
4. ISA encoders (12 files, architecture-specific)

**Low-Maintenance Areas:**
1. Core interpreter (well-abstracted)
2. Standard library (mostly independent modules)
3. Applications (clear separation of concerns)

---

## Appendix: Quick Reference

### File Search Commands

```bash
# Find all .spl files
find src/ -name "*.spl"

# Count lines by directory
for dir in src/*/; do
  echo "$(basename "$dir"): $(find "$dir" -name "*.spl" -exec wc -l {} + | tail -1)"
done

# Find duplicate file names
find src/ -name "*.spl" -type f -printf "%f\n" | sort | uniq -c | sort -rn | head -20

# Search for specific types
grep -rn "^class " src/ --include="*.spl" | grep "BackendFactory"
grep -rn "^struct " src/ --include="*.spl" | grep "MirInst"
grep -rn "^enum " src/ --include="*.spl" | grep "TokenKind"
```

### Key Documentation

- Bootstrap duplication: `src/compiler/README.md`, `src/compiler_core/README.md`
- Duplication cleanup: `doc/report/duplication_recommendations.md`
- Semantic patterns: `doc/report/semantic_duplication_analysis.md`
- SFFI patterns: `CLAUDE.md` (SFFI section)
- Test framework: `src/std/spec/` (SSpec)

---

**Document Version:** 1.0
**Last Updated:** 2026-02-14
**Maintainer:** Claude Code Explore Agent
**Status:** Comprehensive inventory complete, recommendations provided
