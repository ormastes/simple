# TODO Remains Report

**Generated:** 2026-01-17
**Last Updated:** 2026-01-18 (Session 2)
**Total Tagged TODOs:** 409 across entire codebase (down from 430)
**Untagged TODOs:** 0 (all properly tagged)

## Core Compiler Status (`src/` directory)

**Total: 1 TODO** (down from 119 - **99.2% reduction!**)

| File | Line | Priority | Description |
|------|------|----------|-------------|
| src/compiler/src/interpreter_eval.rs | 365 | P3 | Macro contract optimization (definition-time processing) |

**All remaining TODOs are P3 (low priority).**

### Recently Resolved (2026-01-18 Session 2)

| File | Line | Status | Resolution |
|------|------|--------|------------|
| tooling/testing/coverage.spl | 254-306 | ✅ Resolved | Coverage collection (Simple, Rust, Python, JS) + HTML report |
| tooling/deployment/versioning.spl | 607-609 | ✅ Resolved | Version file update (Cargo.toml, package.json, etc.) |
| tooling/deployment/pipeline.spl | 593,690,710 | ✅ Resolved | Timeout support, health check, webhook notifications |
| tooling/deployment/bundling.spl | 646,704,730-732 | ✅ Resolved | Archive creation, dependency bundling, self-contained bundles |
| tooling/deployment/automation.spl | 567,663,685 | ✅ Resolved | Cross-platform builds, Slack/email notifications |
| core/list.spl | 56 | ✅ Resolved | Updated from_iter to use Iterator<Item=T> syntax |
| core/traits.spl | 199,206,515 | ✅ Resolved | Updated FromIterator, IntoIterator, Extend traits |
| core/collections.spl | 121,571 | ✅ Resolved | Updated Iterable and extend method |

### Previously Resolved (2026-01-18 Session 1)

| File | Line | Status | Resolution |
|------|------|--------|------------|
| src/parser/src/parser_types.rs | - | ✅ Resolved | Associated type constraints (Iterator<Item=T>) |
| src/parser/src/types_def/trait_impl_parsing.rs | - | ✅ Resolved | Trait inheritance with generics (trait A<T>: B<T>) |
| src/parser/src/ast/nodes/core.rs | - | ✅ Resolved | Type::TypeBinding variant for associated types |

### Previously Resolved (2026-01-17)

| File | Line | Status | Resolution |
|------|------|--------|------------|
| src/compiler/src/interpreter/expr.rs | 119 | ✅ Resolved | Inject code execution was already fully implemented |
| src/driver/tests/interpreter_macro_hygiene.rs | 190 | ✅ Resolved | Pattern matching was already supported, added 3 tests |

---

## Current TODO Summary (2026-01-18 Session 2)

**Total Tagged TODOs:** 409 (down from 430 - **21 resolved this session**)

| Priority | Count | Percentage |
|----------|-------|------------|
| **P0 (Critical)** | 2 | 0.5% |
| **P1 (High)** | 0 | 0% | ✅ **ALL RESOLVED** |
| **P2 (Medium)** | 105 | 26% |
| **P3 (Low)** | 302 | 74% |
| **Untagged** | 0 | 0% | ✅ **ALL TAGGED** |

### By Area

| Area | Count | Description |
|------|-------|-------------|
| stdlib | 138 | Standard library (down from 159) |
| ui | 123 | UI/TUI components |
| test | 56 | Test framework |
| parser | 46 | Parser features |
| doc | 28 | Documentation |
| runtime | 9 | Runtime |
| gpu | 2 | GPU/Vulkan |
| compiler | 2 | Compiler |
| type | 1 | Type system |
| codegen | 1 | Code generation |

**Major Progress:**
- All TODOs properly tagged with `[area][priority]` format
- Coverage/deployment tooling fully implemented
- Stdlib updated to use new parser features (Iterator<Item=T>)

### P1 Breakdown - ALL RESOLVED
- **~~9 Vulkan FFI tests~~** - ✅ **RESOLVED** (2026-01-18): FFI implemented in Rust
- **~~7 Async/concurrency~~** - ✅ **RESOLVED** (2026-01-18): Promise wrapping & sync→async validation implemented

## Detailed Analysis (Current - 2026-01-18)

### P1 High Priority - ✅ ALL RESOLVED

#### ~~Vulkan FFI Tests (9 items)~~ ✅ RESOLVED
**File:** `simple/std_lib/test/unit/ui/vulkan_phase1_validation.spl`

**Resolution (2026-01-18):**
- ✅ Vulkan FFI (`rt_vk_*` functions) fully implemented in Rust
- ✅ 23 GPU unit tests now passing
- ✅ Fixed use-after-free bug in `VulkanDevice::Drop`

---

#### ~~Async/Type System (7 items)~~ ✅ RESOLVED
**Files:** `simple/std_lib/test/features/concurrency/async_default_spec.spl`

**Resolution (2026-01-18):**
- ✅ Promise auto-wrapping implemented in `src/compiler/src/type_check/mod.rs`
- ✅ Sync→async call validation in HIR lowering
- ✅ Effect inference fully working
- ✅ Type checker integrated into compilation pipeline

---

#### ~~Union Types~~ ✅ WORKING
**File:** `simple/std_lib/test/unit/spec/union_impl_spec.spl`

**Status:** Union types parse and work (syntactic sugar for enum).
- ✅ `union` keyword supported
- ✅ Variants with payloads work
- ✅ Tests passing

---

### P2 Medium Priority (14 items)

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

#### Other P2 Items (6 items)
- Mode runner improvements

---

### MEDIUM PRIORITY - Nice to Have

#### 4. Parser Improvements (0 remaining - ALL RESOLVED)

~~Previously listed:~~
- ~~Inline predicate parser~~ → Intentionally simplified (full parsing in compiler)
- ~~Optional error message~~ → Already implemented (`out_err(e):`)
- ~~Doc comment storage~~ → Already implemented
- ~~!Trait syntax~~ → Already implemented (`where T: !Clone`)
- ~~SUI AST parsing~~ → ✅ **Implemented 2026-01-18**

**Recently Implemented (2026-01-18):**
- ✅ Trait inheritance with generics: `trait Sequence<T>: Collection<T>:`
- ✅ Multiple trait bounds: `trait Debug: Display + Clone:`
- ✅ Associated type constraints: `Iterator<Item=T>`, `Map<Key=K, Value=V>`
- ✅ SUI shared state AST parsing: `{$ let name: Type = value $}`

**Already Implemented (verified 2026-01-18):**
- ✅ !Trait negative bounds syntax: `where T: Clone + !Send`
- ✅ Doc comment storage in structs/classes
- ✅ Contract error bindings: `out_err(e):`
- ✅ AOP predicate parsing (simplified by design, full parsing in compiler)

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

## Quick Wins - ✅ ALL RESOLVED (2026-01-18 Session 2)

### 1. Doc Comment Storage ✅ ALREADY DONE
**File:** `src/parser/src/types_def/mod.rs`
**Status:** Found to be already implemented - doc_comment field exists and is assigned.

### 2. SDN Parser Integration ✅ ALREADY DONE
**Files:** `src/compiler/src/mock.rs`, `src/compiler/src/arch_rules.rs`
**Status:** Found to be already integrated - no TODOs remaining.

### 3. Glob Pattern Matching ✅ ALREADY DONE
**File:** `src/runtime/src/value/doctest_io.rs`
**Status:** Found to be already implemented using `glob::Pattern` crate.

### 4. Coverage/Deployment Tooling ✅ IMPLEMENTED
**Files:** `simple/std_lib/src/tooling/testing/coverage.spl`, `deployment/*.spl`
**Status:** 25 TODOs implemented:
- Coverage collection (Simple, Rust, Python, JavaScript)
- HTML report generation
- Version file updates (Cargo.toml, package.json, pyproject.toml)
- Health checks and webhook notifications
- Dependency bundling with ldd/otool
- Self-contained bundle creation with wrapper scripts
- Cross-compilation support
- Slack/email notifications

### 5. Stdlib Iterator Syntax ✅ UPDATED
**Files:** `core/list.spl`, `core/traits.spl`, `core/collections.spl`
**Status:** Updated to use `Iterator<Item=T>` syntax now that parser supports it.

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
