# Rust to Simple Migration Roadmap

**Date:** 2026-01-21 (Updated)
**Status:** Phase 3-6 Complete + 2 Additional
**Goal:** Build formally verified compiler core in Simple

---

## Completed Migrations ✅

| File | LOC | Pattern | Expansion | Lean-Friendly | Tests |
|------|-----|---------|-----------|---------------|-------|
| **types_util.rs** | 93 | Pure type mapping | +97% | ⭐⭐⭐⭐⭐ | 35 |
| **error_utils.rs** | 61 | Error construction | +115% | ⭐⭐⭐⭐⭐ | 46 |
| **arg_parsing.rs** | 126 | Boolean flags | -28% | ⭐⭐⭐⭐ | 12 |
| **test_args.rs** | 169 | Mutable struct | +16% | ⭐⭐⭐ | 27 |
| **lint_config.rs** | 124 | Config parsing | -6% | ⭐⭐⭐⭐ | 21 |
| **sandbox.rs** | 94 | Builder (blocked) | +171% | ⭐⭐ | 24 |
| **env_commands.rs** | 69 | Subcommand | +54% | ⭐⭐⭐⭐ | 23 |
| **startup.rs** | 86 | State return | +205% | ⭐⭐⭐ | 18 |

**Total:** 16 files, ~1,600 Rust LOC → ~2,570 Simple LOC, 460+ tests

---

## Priority 1: Pure Functional Utilities (Perfect for Lean) 🔥

### ✅ COMPLETED

| File | LOC | Status | Tests | Notes |
|------|-----|--------|-------|-------|
| **hir/types/layout.rs** | ~80 | ✅ Done | (existing) | layout.spl - C ABI alignment |
| **codegen/types_util.rs** | 93 | ✅ Done | 35 | Phase 2 complete |
| **error_utils.rs** | 61 | ✅ Done | 46 | Phase 2 complete |
| **diagnostics/severity.rs** | 98 | ✅ Done | 28 | severity.spl |
| **mir/inst_types.rs** | 180 | ✅ Done | 36 | mir_types.spl - 9 enums |
| **mir/effects.rs** | 140 | ✅ Done | 48 | effects_core.spl - Lean-aligned |
| **lexer/escapes.rs** | 51 | ✅ Done | 32 | string_escape.spl |
| **symbol_hash** | 66 | ✅ Done | 30 | symbol_hash.spl |
| **symbol_analysis** | 71 | ✅ Done | 38 | symbol_analysis.spl |
| **tensor/broadcast.rs** | 95 | ✅ Done | 40 | tensor_broadcast.spl |

**Completed:** ~1,035 Rust LOC → ~1,650 Simple LOC, 333+ tests

### High Priority (This Week)

| File | LOC | Pattern | Predicted | Why Migrate |
|------|-----|---------|-----------|-------------|
| **parser/token_info.rs** | ~150 | Token metadata | +60% | Lexer verification |
| **hir/types/alignment.rs** | ~70 | Alignment rules | +80% | ABI correctness |
| **mir/register_alloc_info.rs** | ~90 | Register metadata | +70% | Register allocation |
| **codegen/calling_convention.rs** | ~110 | ABI mappings | +75% | Function call safety |

**Estimated:** ~420 Rust LOC → ~700 Simple LOC, 80+ tests

---

## Priority 2: String & Data Processing Utilities ⭐⭐⭐⭐⭐

### Very High Priority

| File | LOC | Pattern | Predicted | Why Migrate |
|------|-----|---------|-----------|-------------|
| **string_escape.rs** | ~80 | String escaping | -20% | Pure functions |
| **path_normalize.rs** | ~90 | Path manipulation | -15% | String processing |
| **format_helpers.rs** | ~100 | String formatting | -20% | Pure string ops |
| **parse_number.rs** | ~65 | Number parsing | +10% | Parsing utilities |

**Estimated:** ~335 Rust LOC → ~300 Simple LOC, 60+ tests

---

## Priority 3: Configuration & Parsing (Good Candidates) ⭐⭐⭐⭐

### High Priority

| File | LOC | Pattern | Predicted | Why Migrate |
|------|-----|---------|-----------|-------------|
| **aop_config.rs** | 108 | Config parsing | -5% | Similar to lint_config |
| **runtime/value/ffi/config.rs** | 105 | FFI config | -10% | Config pattern |
| **hir/types/layout_config.rs** | ~80 | Layout config | +10% | Type system config |
| **diagnostics/severity.rs** | ~50 | Severity levels | +20% | Enum mapping |

**Estimated:** ~343 Rust LOC → ~350 Simple LOC, 65+ tests

---

## Priority 4: Interpreter Helpers (Medium Complexity) ⭐⭐⭐

### Medium Priority

| File | LOC | Pattern | Predicted | Why Migrate |
|------|-----|---------|-----------|-------------|
| **interpreter_helpers/utilities.rs** | 283 | Mixed utilities | +10% | Some pure functions |
| **interpreter_helpers/collections.rs** | 290 | Collection ops | -5% | List operations |
| **interpreter_helpers/patterns.rs** | 304 | Pattern matching | -10% | Lean-friendly! |

**Estimated:** ~877 Rust LOC → ~880 Simple LOC, 120+ tests

**Note:** These require careful handling due to interpreter dependencies.

---

## Blocked / Defer ❌

### Blocked by Language Features

| File | LOC | Blocker | When to Migrate |
|------|-----|---------|-----------------|
| **sandbox.rs** | 94 | P0: Struct update syntax | After feature lands |
| All builder patterns | ~15 files | P0: Struct update syntax | After feature lands |

### Not Good Candidates (FFI-Heavy)

| File | LOC | Reason | Alternative |
|------|-----|--------|-------------|
| **elf_utils.rs** | 380 | Binary parsing, unsafe | Keep in Rust |
| **codegen/llvm_*.rs** | ~2000 | LLVM FFI | Keep in Rust |
| **cranelift bindings** | ~5000 | Cranelift FFI | Keep in Rust |

---

## Migration Strategy

### Phase 3: Pure Utilities (Next Session)

**Goal:** Migrate 3-4 pure functional utilities
**Time:** ~6 hours
**Files:**
1. hir/types/layout.rs
2. mir/inst_info.rs
3. parser/token_info.rs
4. (Optional) hir/types/alignment.rs

**Expected Output:**
- ~400 Rust LOC → ~680 Simple LOC
- 70+ comprehensive tests
- 3+ Lean theorems proven

---

### Phase 4: String Utilities (This Week)

**Goal:** Migrate string/path processing
**Time:** ~4 hours
**Files:**
1. string_escape.rs
2. path_normalize.rs
3. format_helpers.rs
4. parse_number.rs

**Expected Output:**
- ~335 Rust LOC → ~300 Simple LOC (code reduction!)
- 60+ tests
- Demonstrate Simple's string handling strength

---

### Phase 5: Configuration Files (Next Week)

**Goal:** Migrate config parsers
**Time:** ~5 hours
**Files:**
1. aop_config.rs
2. runtime/value/ffi/config.rs
3. hir/types/layout_config.rs
4. diagnostics/severity.rs

**Expected Output:**
- ~343 Rust LOC → ~350 Simple LOC
- 65+ tests
- Config pattern library

---

### Phase 6: Interpreter Helpers (Advanced)

**Goal:** Migrate interpreter utilities
**Time:** ~8 hours
**Files:**
1. interpreter_helpers/patterns.rs (highest value!)
2. interpreter_helpers/collections.rs
3. interpreter_helpers/utilities.rs

**Expected Output:**
- ~877 Rust LOC → ~880 Simple LOC
- 120+ tests
- Pattern matching verification

---

## Lean Verification Milestones

### Milestone 1: Core Type System (✅ In Progress)

**Files:**
- ✅ types_util.spl
- ⏳ layout.rs → layout.spl
- ⏳ alignment.rs → alignment.spl

**Theorems to Prove:**
1. Type size bounds (0 ≤ size ≤ 8)
2. Total built-in size (59 bytes)
3. Layout alignment properties
4. Pointer type consistency

---

### Milestone 2: Instruction Metadata

**Files:**
- ⏳ inst_info.rs → inst_info.spl
- ⏳ register_alloc_info.rs → register_info.spl

**Theorems to Prove:**
1. Opcode coverage (all opcodes mapped)
2. Register constraint satisfaction
3. Instruction size bounds
4. Operand type safety

---

### Milestone 3: String Processing

**Files:**
- ⏳ string_escape.rs → string_escape.spl
- ⏳ parse_number.rs → parse_number.spl

**Theorems to Prove:**
1. Escape/unescape bijection
2. Parse inverse of format
3. Number bounds preservation
4. UTF-8 validity

---

### Milestone 4: Pattern Matching

**Files:**
- ⏳ interpreter_helpers/patterns.rs → patterns.spl

**Theorems to Prove:**
1. Exhaustiveness checking correctness
2. Pattern overlap detection
3. Binding extraction soundness
4. Type inference during matching

---

## Success Metrics

### Per-Phase Goals

| Metric | Phase 3 | Phase 4 | Phase 5 | Phase 6 |
|--------|---------|---------|---------|---------|
| **Files** | 3-4 | 4 | 4 | 3 |
| **Rust LOC** | ~400 | ~335 | ~343 | ~877 |
| **Simple LOC** | ~680 | ~300 | ~350 | ~880 |
| **Tests** | 70+ | 60+ | 65+ | 120+ |
| **Coverage** | 100% | 100% | 100% | 95%+ |
| **Theorems** | 3+ | 2+ | 1+ | 5+ |
| **Time** | 6h | 4h | 5h | 8h |

### Cumulative Goals (End of Phase 6)

| Metric | Target |
|--------|--------|
| **Total Files** | 24+ |
| **Total Rust LOC** | ~3,200 |
| **Total Simple LOC** | ~3,500 |
| **Total Tests** | 500+ |
| **Lean Theorems** | 15+ proven |
| **Verified Core** | Type system + Instructions |

---

## File Selection Criteria

### ✅ Good Migration Candidates

**Must have 3+ of:**
- ✅ Pure functions (no side effects)
- ✅ Small file (< 200 LOC)
- ✅ Self-contained (few dependencies)
- ✅ String/data processing
- ✅ Type mappings or enums
- ✅ Mathematical properties
- ✅ Clear test scenarios

**Examples:**
- types_util.rs ✅✅✅✅✅✅✅ (Perfect!)
- error_utils.rs ✅✅✅✅✅✅ (Excellent!)

---

### ❌ Poor Migration Candidates

**Avoid if has 2+ of:**
- ❌ Heavy FFI usage
- ❌ Unsafe code
- ❌ Complex state management
- ❌ Builder patterns (until P0 fix)
- ❌ Deep integration with Rust libs
- ❌ Performance-critical (no benchmarks)

**Examples:**
- elf_utils.rs ❌❌❌ (Binary parsing, unsafe)
- llvm bindings ❌❌❌❌ (FFI, unsafe, complex)

---

## Pattern Library (Established)

| # | Pattern | Change | Lean | Use When |
|---|---------|--------|------|----------|
| 1 | Boolean Flags | -28% | ⭐⭐⭐⭐ | CLI parsing |
| 2 | Mutable Struct | -4% | ⭐⭐⭐ | Config building |
| 3 | String Processing | -20% | ⭐⭐⭐⭐⭐ | Text utilities |
| 4 | Builder (blocked) | +171% | ⭐⭐ | **Avoid!** |
| 5 | List Operations | -15% | ⭐⭐⭐⭐⭐ | Data transform |
| 6 | Option/Result | +15% | ⭐⭐⭐ | Error handling |
| 7 | Enums | -60% | ⭐⭐⭐⭐⭐ | State machines |
| 8 | Struct Defaults | +150% | ⭐⭐ | **Defer P1** |
| 9 | Subcommand Dispatch | +38% | ⭐⭐⭐⭐ | CLI routers |
| 10 | State Return | +39% | ⭐⭐⭐⭐⭐ | Immutable updates |
| **11** | **Pure Type Mapping** | **+97%** | **⭐⭐⭐⭐⭐** | **Codegen** |
| **12** | **Error Construction** | **+115%** | **⭐⭐⭐⭐⭐** | **Diagnostics** |

---

## Next Actions

### Immediate (This Session)

- [x] Migrate types_util.rs
- [x] Migrate error_utils.rs
- [x] Write 81 comprehensive tests
- [x] Create migration reports

### Next Session

- [ ] Migrate hir/types/layout.rs
- [ ] Migrate mir/inst_info.rs
- [ ] Migrate parser/token_info.rs
- [ ] Prove 3+ Lean theorems
- [ ] Document Lean verification workflow

### This Week

- [ ] Complete Phase 3 (pure utilities)
- [ ] Complete Phase 4 (string utilities)
- [ ] Establish CI/CD for Simple code
- [ ] Document migration patterns

### This Month

- [ ] Complete Phase 5-6
- [ ] 15+ Lean theorems proven
- [ ] Verified compiler core established
- [ ] Migration guide published

---

**Current Status:** 16 files migrated, 460+ tests, 12+ patterns established

**Next Milestone:** Prove Lean theorems for effects_core.spl and tensor_broadcast.spl

**Long-Term Goal:** Formally verified Simple compiler core

---

## Recent Progress (2026-01-21)

### Session 1: Phases 3-6
- ✅ 6 modules migrated (layout, string_escape, severity, symbol_hash, symbol_analysis, effects_core)
- ✅ 176+ tests, 100% coverage
- ✅ effects_core.spl: Perfect 1:1 Lean alignment

### Session 2: Continuation
- ✅ 2 modules migrated (tensor_broadcast, mir_types)
- ✅ 76 tests, 100% coverage
- ✅ NumPy broadcasting semantics
- ✅ 9 MIR enum types with utilities

**See Reports:**
- `doc/09_report/rust_to_simple_migration_phases3-6_2026-01-21.md`
- `doc/09_report/rust_to_simple_migration_continuation_2026-01-21.md`
