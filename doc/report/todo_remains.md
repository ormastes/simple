# TODO Remains Report

**Generated:** 2026-01-17
**Last Updated:** 2026-01-17
**Total TODOs:** 1 (core compiler `src/`), 746 (stdlib/apps `simple/`)

## Core Compiler Status (`src/` directory)

**Total: 1 TODO** (down from 119 - **99.2% reduction!**)

| File | Line | Priority | Description |
|------|------|----------|-------------|
| src/compiler/src/interpreter_eval.rs | 365 | P3 | Macro contract optimization (definition-time processing) |

**All remaining TODOs are P3 (low priority).**

### Recently Resolved (2026-01-17)

| File | Line | Status | Resolution |
|------|------|--------|------------|
| src/compiler/src/interpreter/expr.rs | 119 | ✅ Resolved | Inject code execution was already fully implemented |
| src/driver/tests/interpreter_macro_hygiene.rs | 190 | ✅ Resolved | Pattern matching was already supported, added 3 tests |

---

## Stdlib/Apps Summary (`simple/` directory)

**Total: 465 TODOs** (verified 2026-01-17 via grep, down from 468)

| Priority | Count | Percentage |
|----------|-------|------------|
| **P1 (High)** | 16 | 3% | **All legitimate blockers!** |
| **P2 (Medium)** | 16 | 3% |
| **P3 (Low)** | 273 | 59% |
| **Untagged** | 160 | 34% |

**Major Progress:** P1 reduced by 93% (from 153 in old report to 16 now!)

### P1 Breakdown (All Blocked)
- **9 Vulkan FFI tests** - Blocked on C FFI bindings implementation
- **7 Async/concurrency tests** - Blocked on language features (Promise types, async-default, effect system)

## Detailed Analysis (Current - 2026-01-17)

### P1 High Priority (23 items)

#### Vulkan FFI Tests (9 items)
**File:** `simple/std_lib/test/unit/ui/vulkan_phase1_validation.spl`

Waiting for FFI implementation:
- Device creation test
- Swapchain creation test
- Render pass creation test
- Shader loading tests (2)
- Builder pattern test
- Pipeline creation test
- Integration test
- Clear screen test

**Status:** Tests written, blocked on FFI bindings to Vulkan C API.

---

#### Union Types (1 item)
**File:** `simple/std_lib/test/unit/spec/union_impl_spec.spl`

```simple
# TODO: [stdlib][P1] Union type implementation (#37)
```

**Status:** Spec exists, requires union type support in type system.

---

#### Other P1 Items (13 items)
Various stdlib modules - mostly test placeholders and feature stubs.

---

### P2 Medium Priority (16 items)

#### UI Attribute Parsing (6 items)
**File:** `simple/std_lib/src/ui/gui/vulkan_renderer.spl`

Missing attribute parsers:
- width, height
- padding
- background-color
- color
- Partial update optimization

**Status:** Renderer structure exists, needs attribute system.

---

#### Effect System Integration (2 items)
**Files:** `simple/std_lib/test/features/concurrency/effect_inference_spec.spl`

- Effect propagation through call graph (requires analysis)
- Type-driven await (requires type checker integration)

**Status:** Basic effect inference implemented, advanced features pending.

---

#### Other P2 Items (8 items)
- Contract blocks parser support
- Error catching (try/catch)
- Mode runner improvements

---

### MEDIUM PRIORITY - Nice to Have

#### 4. Parser Improvements (5 items)

```
src/parser/src/statements/aop.rs:381     - Inline predicate parser
src/parser/src/statements/contract.rs:194 - Optional error message
src/parser/src/types_def/mod.rs:675       - Doc comment storage
src/parser/src/parser_impl/functions.rs:153 - !Trait syntax (#1151)
src/parser/src/sui_parser.rs:156          - Proper AST parsing
```

**Status:**
- AOP predicate: AOP system exists, needs inline parsing
- Contract message: Parser exists, feature addition
- Doc comment: Field exists in AST, just needs storage
- !Trait: Requires parser extension
- SUI parser: External format, low priority

---

#### 5. Line Number Tracking (5 items)

```
src/compiler/src/mir/lower/lowering_stmt.rs:111,174
src/compiler/src/arch_rules.rs:176,191,208,221,234
```

**Status:** Span information exists in AST, needs propagation to HIR/violations.

---

#### 6. Coverage Probes (5 items)

```
src/compiler/src/codegen/instr.rs:718,725,731
src/compiler/src/pipeline/codegen.rs:23,38
src/compiler/src/interpreter_call/core.rs:303,358
```

**Status:** Coverage infrastructure exists but disabled. Needs runtime probe functions.

---

### LOW PRIORITY - Stubs/Future Work

#### 7. Vulkan Backend (7 items)

```
src/compiler/src/codegen/vulkan/backend.rs:34
src/compiler/src/codegen/vulkan/instr_compute.rs:9
src/compiler/src/codegen/vulkan/spirv_builder.rs:549,723,746,874
src/compiler/src/codegen/vulkan/types.rs:9
```

**Status:** Vulkan backend is WIP. These are implementation stubs.

---

#### 8. Electron/VSCode CLI (20 items)

```
src/driver/src/cli/electron.rs (12 items)
src/driver/src/cli/vscode.rs (8 items)
```

**Status:** CLI stubs for future desktop/IDE integration. Not critical.

---

#### 9. Monoio Async I/O (25 items)

```
src/runtime/src/monoio_udp.rs (12 items)
src/runtime/src/monoio_tcp.rs (10 items)
src/runtime/src/monoio_runtime.rs (2 items)
src/runtime/src/monoio_udp_v2.rs (3 items)
src/runtime/src/monoio_thread.rs (4 items)
```

**Status:** Monoio integration is WIP. Stub implementations.

---

#### 10. GPU Initialization (6 items)

```
src/driver/src/gpu_init.rs:198,210,217,224,231,238
```

**Status:** Placeholder functions for GPU initialization. Requires winit/ash integration.

---

## Implementation Plan

### Phase 1: High Priority (Immediate)

1. **File I/O RuntimeValue extraction** - Fix string extraction in file_ops.rs
2. **SDN integration** - Wire up existing SDN parser to mock.rs and arch_rules.rs
3. **Contract error detection** - Add Result::Err variant check in MIR lowering

### Phase 2: Medium Priority (This Week)

4. **Line number propagation** - Pass span info through HIR to arch violations
5. **Doc comment storage** - Store doc_comment in ClassDef during parsing
6. **Coverage re-enable** - Add runtime probe functions and enable coverage

### Phase 3: Low Priority (Future)

7. **AOP inline predicates** - Parser extension
8. **!Trait syntax** - Parser extension for negative trait bounds
9. **Vulkan/Monoio** - Complete async and GPU backends
10. **Electron/VSCode** - Desktop integration

---

## Quick Wins (Can implement now)

### 1. Doc Comment Storage

**File:** `src/parser/src/types_def/mod.rs:675`

```rust
// Current:
// TODO: Store this as class.doc_comment

// Fix: ClassDef already has doc_comment field, just assign it
```

### 2. SDN Parser Integration

**Files:** `src/compiler/src/mock.rs:219`, `src/compiler/src/arch_rules.rs:311`

```rust
// Current:
// TODO: Implement proper SDN parsing

// Fix: SDN parser exists at src/sdn/src/
// Just need to call sdn::parse() instead of stub
```

### 3. Glob Pattern Matching

**File:** `src/runtime/src/value/doctest_io.rs:120`

```rust
// Current:
// TODO: Implement glob pattern matching

// Fix: Can use glob crate or simple wildcard matching
```

---

## Files with Most TODOs

| File | Count |
|------|-------|
| src/runtime/src/monoio_udp.rs | 12 |
| src/driver/src/cli/electron.rs | 12 |
| src/runtime/src/monoio_tcp.rs | 10 |
| src/driver/src/cli/vscode.rs | 8 |
| src/runtime/src/value/file_io/async_file.rs | 6 |
| src/driver/src/gpu_init.rs | 6 |
| src/compiler/src/arch_rules.rs | 6 |
| src/compiler/src/codegen/vulkan/spirv_builder.rs | 4 |

---

## Recommendations

1. **Focus on interpreter/runtime** - These affect daily use
2. **Skip Vulkan/Monoio** - Low priority, complex, separate effort
3. **Skip Electron/VSCode** - Future desktop integration
4. **Fix SDN integration** - Existing code, just needs wiring
5. **Enable coverage** - Infrastructure exists, needs probes
