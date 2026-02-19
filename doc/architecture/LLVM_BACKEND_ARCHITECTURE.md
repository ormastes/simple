# LLVM Backend Architecture

**Status**: Planned (2026-02-13)
**Related**: LLVM_BACKEND_UNIFICATION_PLAN.md

---

## Current Architecture (Before Unification)

```
┌─────────────────────────────────────────────────────────────┐
│                    LLVM Toolchain                            │
│  (llc, opt, clang - external dependencies)                  │
└─────────────────────────────────────────────────────────────┘
                            ▲
                            │
        ┌───────────────────┼───────────────────┐
        │                   │                   │
┌───────▼────────┐  ┌───────▼────────┐  ┌──────▼──────┐
│  Full Simple   │  │  Core Simple   │  │ llvm_direct │
│    Backend     │  │    Backend     │  │  (hybrid)   │
│                │  │                │  │             │
│  compiler/     │  │ compiler_core_legacy/ │  │ app/compile/│
│  backend/      │  │ backend/       │  │             │
│                │  │                │  │             │
│ ├─ llvm_backend│  │├─ llvm_backend │  │ C→LLVM path │
│ ├─ llvm_ir_*   │  │├─ llvm_ir_*    │  │             │
│ ├─ llvm_target │  │├─ llvm_target  │  │             │
│ ├─ llvm_tools  │  │├─ llvm_tools   │  │             │
│ └─ llvm_type_* │  │└─ llvm_type_*  │  │             │
│                │  │                │  │             │
│ ~2,377 lines   │  │ ~1,098 lines   │  │  ~200 lines │
└────────────────┘  └────────────────┘  └─────────────┘
        │                   │
        │ DUPLICATION: ~1,300 lines (~50%)
        │  - llvm_tools: 100% identical
        │  - llvm_target: 80% similar
        │  - llvm_backend: 60% similar
        └───────────────────┘

     Total: ~3,475 lines
```

### Problems

1. **Code Duplication**: ~1,300 lines duplicated (~37% of total)
2. **Maintenance Burden**: Bug fixes need 2 changes
3. **Inconsistency Risk**: Changes to Full might not sync to Core
4. **Testing Overhead**: Same tests duplicated for both backends

---

## Planned Architecture (After Unification)

```
┌─────────────────────────────────────────────────────────────┐
│                    LLVM Toolchain                            │
│  (llc, opt, clang - external dependencies)                  │
└─────────────────────────────────────────────────────────────┘
                            ▲
                            │
        ┌───────────────────┴───────────────────┐
        │                                       │
┌───────▼─────────────────────────────┐  ┌──────▼──────┐
│    Shared LLVM Infrastructure       │  │ llvm_direct │
│                                     │  │  (hybrid)   │
│    src/shared/llvm/                 │  │             │
│                                     │  │ app/compile/│
│  ├─ mod.spl (public API)            │  │             │
│  ├─ target.spl (triples, CPUs)      │  │ C→LLVM path │
│  ├─ tools.spl (llc, opt, clang)     │  │             │
│  ├─ types.spl (primitive mappings)  │  │             │
│  ├─ passes.spl (optimization passes)│  │             │
│  └─ ir_primitives.spl               │  │             │
│                                     │  │             │
│  ~800 lines                         │  │  ~200 lines │
│  (Bootstrap-compatible:             │  └─────────────┘
│   No generics, no Option types)     │
└─────────────────────────────────────┘
        ▲                   ▲
        │                   │
┌───────┴────────┐  ┌───────┴────────┐
│  Full Simple   │  │  Core Simple   │
│  LLVM Wrapper  │  │  LLVM Wrapper  │
│                │  │                │
│  compiler/     │  │ compiler_core_legacy/ │
│  backend/      │  │ backend/       │
│                │  │                │
│ ├─ llvm_backend│  │├─ llvm_backend │
│ │  (uses       │  ││  (uses        │
│ │   shared)    │  ││   shared)     │
│ ├─ llvm_ir_*   │  │├─ llvm_ir_*    │
│ │  (Full MIR→  │  ││  (Core MIR→   │
│ │   LLVM)      │  ││   LLVM)       │
│ └─ llvm_type_* │  │└─ llvm_type_*  │
│    (Full types)│  │   (Core types) │
│                │  │                │
│ ~1,200 lines   │  │ ~500 lines     │
└────────────────┘  └────────────────┘

     Total: ~2,500 lines (28% reduction)
     Shared: ~800 lines (32% of total)
```

### Benefits

1. **Reduced Duplication**: ~975 lines eliminated
2. **Single Source of Truth**: Bug fixes in 1 place
3. **Consistent Behavior**: Both backends use same infrastructure
4. **Easier Testing**: Test shared code once
5. **Faster Development**: New features added once

---

## Component Responsibilities

### Shared Library (shared/llvm/)

**Responsibilities**:
- Target configuration (triples, CPU selection, features)
- LLVM tool invocations (llc, opt, clang command generation)
- Primitive type mapping (i64, f64, bool, ptr, void → LLVM)
- Optimization pass definitions (pass names, flags, selection)
- Common IR building primitives

**Constraints**:
- MUST be Core Simple compatible (seed_cpp can compile)
- NO generics (`Vec<T>` → `[T]`)
- NO Option types (`text?` → `text` with nil)
- NO advanced pattern matching

**Example Functions**:
```simple
# Target triple generation
fn llvm_triple_for_target(target: CodegenTarget, baremetal: bool) -> LlvmTargetTriple

# CPU selection (with compatibility mode)
fn llvm_cpu_for_target(target: CodegenTarget, compat: bool) -> text

# Optimization pass selection
fn passes_for_opt_level(level: i64) -> [LlvmPass]

# Tool invocation
fn invoke_llc(input: text, output: text, triple: text, cpu: text, opt: text) -> i64
```

### Full Simple Backend (compiler/backend/)

**Responsibilities**:
- Full Simple MIR → LLVM IR translation
- Full Simple type mapping (structs, enums, generics)
- Backend API implementation (CompilerBackend trait)
- Integration with Full Simple compiler pipeline

**Uses from shared**:
- Target configuration
- LLVM tool invocations
- Primitive type mappings
- Optimization passes

**Compiler-specific**:
- Generic type translation (`Vec<T>` → LLVM)
- Option type handling (`Option<T>` → LLVM tagged union)
- Advanced pattern matching codegen
- Full Simple-specific optimizations

### Core Simple Backend (compiler_core_legacy/backend/)

**Responsibilities**:
- Core Simple MIR → LLVM IR translation
- Core Simple type mapping (desugared structs, simple enums)
- Backend API implementation (CoreBackend trait)
- Integration with Core Simple compiler pipeline

**Uses from shared**:
- Target configuration
- LLVM tool invocations
- Primitive type mappings
- Optimization passes

**Compiler-specific**:
- Desugared struct translation
- Simple enum translation (no data variants)
- Basic pattern matching codegen
- Bootstrap-compatible code only

---

## Data Flow

### Compilation Pipeline

```
┌────────────────┐
│ Simple Source  │
└────────┬───────┘
         │
    ┌────▼─────┐
    │  Parser  │
    └────┬─────┘
         │
    ┌────▼─────┐
    │   AST    │
    └────┬─────┘
         │
    ┌────▼─────┐
    │   HIR    │
    └────┬─────┘
         │
    ┌────▼─────┐
    │   MIR    │◄────── Compiler-specific MIR representation
    └────┬─────┘        (Full: rich types, Core: desugared)
         │
         │ ┌──────────────────────────────────────────┐
         ├─► MIR → LLVM IR Builder                    │
         │ │  (Compiler-specific)                     │
         │ │                                          │
         │ │  Uses shared:                            │
         │ │  - shared.llvm.types (primitives)        │
         │ │  - shared.llvm.target (triple, CPU)      │
         │ └──────────────────────────────────────────┘
         │
    ┌────▼─────┐
    │ LLVM IR  │
    └────┬─────┘
         │
         │ ┌──────────────────────────────────────────┐
         ├─► Optimization                             │
         │ │  (shared.llvm.passes)                    │
         │ │                                          │
         │ │  Uses shared:                            │
         │ │  - passes_for_opt_level()                │
         │ │  - invoke_opt()                          │
         │ └──────────────────────────────────────────┘
         │
    ┌────▼─────┐
    │ LLVM IR  │
    │(optimized)│
    └────┬─────┘
         │
         │ ┌──────────────────────────────────────────┐
         ├─► Code Generation                          │
         │ │  (shared.llvm.tools)                     │
         │ │                                          │
         │ │  Uses shared:                            │
         │ │  - invoke_llc()                          │
         │ │  - Target triple from shared             │
         │ └──────────────────────────────────────────┘
         │
    ┌────▼─────┐
    │ Object   │
    │  Code    │
    └────┬─────┘
         │
    ┌────▼─────┐
    │ Linking  │
    └────┬─────┘
         │
    ┌────▼─────┐
    │  Binary  │
    └──────────┘
```

---

## Migration Strategy

### Phase-by-Phase Extraction

**Phase 1: Tools** (100% identical code)
```
Before:
  compiler/backend/llvm_tools.spl (85 lines)
  compiler_core_legacy/backend/llvm_tools.spl (85 lines)

After:
  shared/llvm/tools.spl (85 lines)
  compiler/backend/llvm_backend.spl (imports tools)
  compiler_core_legacy/backend/llvm_backend.spl (imports tools)

Savings: 85 lines (50% reduction in tools)
```

**Phase 2: Target** (~80% similar code)
```
Before:
  compiler/backend/llvm_target.spl (363 lines)
  compiler_core_legacy/backend/llvm_target.spl (230 lines)

After:
  shared/llvm/target.spl (~200 lines shared)
  compiler/backend/llvm_target.spl (~100 lines Full-specific)
  compiler_core_legacy/backend/llvm_target.spl (~50 lines Core-specific)

Savings: ~240 lines (40% reduction in target)
```

**Phase 3: Types** (~30% similar code)
```
Before:
  compiler/backend/llvm_type_mapper.spl (304 lines)
  compiler_core_legacy/backend/llvm_type_mapper.spl (108 lines)

After:
  shared/llvm/types.spl (~80 lines shared primitives)
  compiler/backend/llvm_type_mapper.spl (~220 lines Full types)
  compiler_core_legacy/backend/llvm_type_mapper.spl (~60 lines Core types)

Savings: ~50 lines (12% reduction in types)
```

**Phase 4: Passes** (~90% similar code)
```
Before:
  Passes embedded in llvm_ir_builder.spl (~200 lines in each)

After:
  shared/llvm/passes.spl (~150 lines shared)
  Passes configuration in backends (~50 lines each)

Savings: ~200 lines (50% reduction in pass logic)
```

---

## Testing Strategy

### Unit Tests

```
test/unit/shared/llvm/
  ├── target_spec.spl       # Target triple generation
  ├── tools_spec.spl        # Tool invocation
  ├── types_spec.spl        # Type mapping
  └── passes_spec.spl       # Pass selection
```

### Integration Tests

```
test/integration/
  └── llvm_backend_e2e_spec.spl   # End-to-end compilation
```

### Parity Tests

```
test/system/
  └── backend_parity_spec.spl     # Verify Core == Full output
```

### Test Matrix

| Test Type | Full Backend | Core Backend | Shared Library |
|-----------|-------------|-------------|----------------|
| Unit | ✓ Existing | ✓ Existing | ✓ NEW |
| Feature | ✓ Existing | ✓ Existing | ✓ Covered by backends |
| Integration | ✓ Existing | ✓ Existing | ✓ Covered by backends |
| Parity | - | - | ✓ NEW |
| Bootstrap | ✓ Existing | ✓ Existing | ✓ Covered by bootstrap |

---

## Performance Considerations

### Compilation Time

**Expected**: NO CHANGE
- Shared library is compile-time abstraction
- No additional function calls at runtime
- LLVM IR generation same as before

**Verification**:
```bash
# Before refactoring
time bin/simple build src/compiler/ --backend=llvm

# After refactoring
time bin/simple build src/compiler/ --backend=llvm

# Difference should be <5%
```

### Generated Code Quality

**Expected**: IDENTICAL
- Same LLVM IR generated
- Same optimization passes
- Same LLVM version

**Verification**:
```bash
# Compare generated LLVM IR
diff <(bin/simple build test.spl --emit-llvm-ir --backend=llvm-before) \
     <(bin/simple build test.spl --emit-llvm-ir --backend=llvm-after)

# Should be identical (modulo metadata)
```

### Memory Usage

**Expected**: NEGLIGIBLE INCREASE
- Shared library adds ~800 lines in memory
- But removes ~1,300 duplicated lines
- Net reduction in total code size

---

## Open Questions

1. **Module Location**: `src/shared/llvm/` or `src/std/llvm/`?
   - **Recommendation**: `src/shared/llvm/` (not part of std library)

2. **CLI Exposure**: Expose `--backend=llvm-core` flag?
   - **Recommendation**: No (keep internal, both use same shared code)

3. **IR Primitives**: Extract IR building blocks to shared?
   - **Recommendation**: Yes, in Phase 6 (optional enhancement)

4. **LLVM Version**: Minimum version to support?
   - **Recommendation**: LLVM 15+ (opaque pointers)

5. **Version Detection**: Add LLVM version check?
   - **Recommendation**: Yes (fail fast on old LLVM)

---

**Next Steps**: See LLVM_BACKEND_UNIFICATION_PLAN.md for implementation plan
