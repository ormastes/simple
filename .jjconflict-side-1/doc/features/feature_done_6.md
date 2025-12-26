# Simple Language Features - Archived (Set 6)

**Archive Date:** 2025-12-22
**Total Features:** 57

This file contains completed features extracted from `feature.md` to reduce its size.

## Build & Linker Optimization (#800-824) ✅ Complete

Mold-inspired compilation pipeline optimizations for faster builds.

**Documentation:**
- [mold_linker_analysis.md](../research/mold_linker_analysis.md) - Mold linker integration analysis
- [src_to_bin_optimization.md](../research/src_to_bin_optimization.md) - Full pipeline optimization guide

### Mold Linker Integration (#800-805)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #800 | Mold detection | ✅ | R | [mold_linker_analysis.md](../research/mold_linker_analysis.md) | - | `src/compiler/src/linker/native.rs` |
| #801 | `--linker` CLI flag | ✅ | R | [mold_linker_analysis.md](../research/mold_linker_analysis.md) | - | `src/driver/src/main.rs` |
| #802 | LLVM backend integration | ✅ | R | [mold_linker_analysis.md](../research/mold_linker_analysis.md) | - | `src/compiler/src/codegen/llvm/mod.rs` |
| #803 | Fallback to lld | ✅ | R | [mold_linker_analysis.md](../research/mold_linker_analysis.md) | - | `src/compiler/src/linker/native.rs` |
| #804 | Symbol analysis | ✅ | R | [mold_linker_analysis.md](../research/mold_linker_analysis.md) | - | `src/compiler/src/linker/analysis.rs` |
| #805 | RISC-V 32-bit cross-compile | ✅ | R | [mold_linker_analysis.md](../research/mold_linker_analysis.md) | - | `src/compiler/src/codegen/llvm/` |

**Implemented Features:**
- `NativeLinker` enum with Mold/Lld/Ld variants (`src/compiler/src/linker/native.rs`)
- Auto-detection with fallback chain: mold → lld → ld
- `LinkerBuilder` fluent API for configuration
- `LinkOptions` for library linking, stripping, PIE, shared libs
- `LinkerError` types with symbol extraction from error messages
- CLI: `simple linkers` command to list available linkers
- CLI: `--linker <name>` flag for explicit linker selection
- Environment: `SIMPLE_LINKER`, `SIMPLE_LINKER_THREADS`, `SIMPLE_LINKER_DEBUG`

**Expected Impact:** 4x faster native linking, 35% faster native builds

### Parallelization (#806-812)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #806 | Parallel file parsing | ✅ | R | [src_to_bin_optimization.md](../research/src_to_bin_optimization.md) | - | `src/compiler/src/parallel.rs` |
| #807 | Parallel HIR lowering | ✅ | R | [src_to_bin_optimization.md](../research/src_to_bin_optimization.md) | - | `src/compiler/src/hir/lower/parallel.rs` |
| #808 | Parallel monomorphization | ✅ | R | [src_to_bin_optimization.md](../research/src_to_bin_optimization.md) | - | `src/compiler/src/monomorphize/parallel.rs` |
| #809 | Parallel MIR lowering | ✅ | R | [src_to_bin_optimization.md](../research/src_to_bin_optimization.md) | - | `src/compiler/src/mir/parallel.rs` |
| #810 | Parallel codegen | ✅ | R | [src_to_bin_optimization.md](../research/src_to_bin_optimization.md) | - | `src/compiler/src/codegen/parallel.rs` |
| #811 | Parallel SMF linking | ✅ | R | [src_to_bin_optimization.md](../research/src_to_bin_optimization.md) | - | `src/compiler/src/linker/parallel.rs` |
| #812 | Pipeline parallelism | ✅ | R | [src_to_bin_optimization.md](../research/src_to_bin_optimization.md) | - | `src/compiler/src/pipeline_parallel.rs` |

**Expected Impact:** 8-10x speedup for 10+ file projects

### String Interning (#813-815)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #813 | Parser string interning | ✅ | R | [src_to_bin_optimization.md](../research/src_to_bin_optimization.md) | - | `src/parser/src/interner.rs` |
| #814 | Linker symbol interning | ✅ | R | [src_to_bin_optimization.md](../research/src_to_bin_optimization.md) | - | `src/compiler/src/linker/interner.rs` |
| #815 | Hash precomputation | ✅ | R | [src_to_bin_optimization.md](../research/src_to_bin_optimization.md) | - | `src/compiler/src/linker/interner.rs` |

**Expected Impact:** 25% speedup, 67% memory reduction for strings

### Memory Optimization (#816-820)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #816 | AST arena allocation | ✅ | R | [src_to_bin_optimization.md](../research/src_to_bin_optimization.md) | - | `src/parser/src/arena.rs` |
| #817 | HIR arena allocation | ✅ | R | [src_to_bin_optimization.md](../research/src_to_bin_optimization.md) | - | `src/compiler/src/hir/arena.rs` |
| #818 | MIR arena allocation | ✅ | R | [src_to_bin_optimization.md](../research/src_to_bin_optimization.md) | - | `src/compiler/src/mir/arena.rs` |
| #819 | Code buffer pooling | ✅ | R | [src_to_bin_optimization.md](../research/src_to_bin_optimization.md) | - | `src/compiler/src/codegen/buffer_pool.rs` |
| #820 | Memory-mapped file reading | ✅ | R | [src_to_bin_optimization.md](../research/src_to_bin_optimization.md) | - | `src/common/src/file_reader.rs` |

**Expected Impact:** 36% memory reduction, 15% speedup

### Caching (#821-824)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #821 | Monomorphization cache | ✅ | R | [src_to_bin_optimization.md](../research/src_to_bin_optimization.md) | - | `src/compiler/src/monomorphize/cache.rs` |
| #822 | Effect analysis cache | ✅ | R | [src_to_bin_optimization.md](../research/src_to_bin_optimization.md) | - | `src/compiler/src/effects_cache.rs` |
| #823 | Incremental compilation | ✅ | R | [src_to_bin_optimization.md](../research/src_to_bin_optimization.md) | - | `src/compiler/src/incremental.rs` |
| #824 | `--parallel` / `--profile` flags | ✅ | R | [src_to_bin_optimization.md](../research/src_to_bin_optimization.md) | - | `src/driver/src/compile_options.rs` |

**Expected Impact:** 3x speedup for incremental builds

**Projected Overall Impact:**
- Single-file: 2.3x faster (2100ms → 917ms)
- Multi-file (10 files): 10.2x faster (21s → 2s)

---

## Module Privacy & Explicit Proxying (#48-49) ✅

When `__init__.spl` is present, child directories are private by default and require explicit proxying.

**Documentation:**
- [spec/modules.md](../spec/modules.md) - Module system specification

### Module Privacy Features (#48-49)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #48 | `__init__.spl` child directory access prevention | ✅ | R | [spec/modules.md](../spec/modules.md) | - | `src/compiler/src/module_resolver.rs` |
| #49 | Explicit proxy exports in `__init__.spl` | ✅ | R | [spec/modules.md](../spec/modules.md) | - | `src/compiler/src/module_resolver.rs` |

**Module Privacy Rules:**
```
+------------------------------------------------------------------+
| RULE                                  | BEHAVIOR                  |
+------------------------------------------------------------------+
| __init__.spl present                  | Children are PRIVATE      |
| No __init__.spl                       | Children are PUBLIC       |
| Child access without proxy            | Compile ERROR             |
| Explicit proxy via `pub use`          | Child becomes PUBLIC      |
+------------------------------------------------------------------+
```

**Directory Structure Example:**
```
mypackage/
├── __init__.spl          # Makes children private
├── public_api.spl        # Explicitly exported via __init__.spl
├── internal/             # PRIVATE - no direct access allowed
│   ├── __init__.spl      # Also makes its children private
│   ├── helper.spl        # Private to internal/
│   └── utils.spl         # Private to internal/
└── models/               # PRIVATE unless proxied
    └── user.spl
```

**`__init__.spl` Explicit Proxying:**
```spl
# mypackage/__init__.spl

mod mypackage

# Explicit public exports (proxy)
pub use public_api.*           # Makes public_api.spl contents public
pub use models.User            # Exports only User from models/

# Private - NOT exported (no pub)
use internal.*                 # Internal use only

# Re-export with rename
pub use models.UserProfile as Profile
```

**Access Rules:**
```spl
# ALLOWED - explicitly proxied
use mypackage.public_api.MyClass    # ✓ proxied via pub use
use mypackage.User                  # ✓ proxied via pub use

# FORBIDDEN - child not proxied
use mypackage.internal.helper       # ✗ Error: internal is private
use mypackage.models.user.UserData  # ✗ Error: UserData not exported
```

---

## Formatting and Lints (#1131-1145) ✅

Deterministic formatting and semantic lint set for code quality.

**Documentation:**
- [spec/formatting_lints.md](../spec/formatting_lints.md) - Formatting and Lints Specification

### Canonical Formatter (#1131-1133)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #1131 | Canonical formatter (no config) | ✅ | R | [formatting_lints.md](../spec/formatting_lints.md) | - | `src/driver/tests/` |
| #1132 | Formatter CLI (`simple fmt`) | ✅ | R | [formatting_lints.md](../spec/formatting_lints.md) | - | `src/driver/tests/` |
| #1133 | Format-on-save IDE integration | ✅ | R | [formatting_lints.md](../spec/formatting_lints.md) | - | - |

### Semantic Lints (#1134-1138)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #1134 | Safety lint set | ✅ | R | [formatting_lints.md](../spec/formatting_lints.md) | - | `src/compiler/tests/` |
| #1135 | Correctness lint set | ✅ | R | [formatting_lints.md](../spec/formatting_lints.md) | - | `src/compiler/tests/` |
| #1136 | Warning lint set | ✅ | R | [formatting_lints.md](../spec/formatting_lints.md) | - | `src/compiler/tests/` |
| #1137 | Style lint set | ✅ | R | [formatting_lints.md](../spec/formatting_lints.md) | - | `src/compiler/tests/` |
| #1138 | Concurrency lint set | ✅ | R | [formatting_lints.md](../spec/formatting_lints.md) | - | `src/compiler/tests/` |

### Lint Control (#1139-1145)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #1139 | `#[allow]`/`#[deny]`/`#[warn]` attributes | ✅ | R | [formatting_lints.md](../spec/formatting_lints.md) | - | `src/parser/tests/` |
| #1140 | Lint groups | ✅ | R | [formatting_lints.md](../spec/formatting_lints.md) | - | `src/compiler/tests/` |
| #1141 | Fix-it hints in diagnostics | ✅ | R | [formatting_lints.md](../spec/formatting_lints.md) | - | `src/compiler/tests/` |
| #1142 | Auto-fix CLI (`simple fix`) | ✅ | R | [formatting_lints.md](../spec/formatting_lints.md) | - | `src/driver/tests/` |
| #1143 | Error code stability | ✅ | R | [formatting_lints.md](../spec/formatting_lints.md) | - | `src/compiler/tests/` |
| #1144 | Lint configuration in simple.sdn | ✅ | R | [formatting_lints.md](../spec/formatting_lints.md) | - | `src/driver/tests/` |
| #1145 | `--explain` for error codes | ✅ | R | [formatting_lints.md](../spec/formatting_lints.md) | - | `src/driver/tests/` |

---

## Trait Coherence (#1146-1155) ✅

Trait implementation rules for unambiguous dispatch and type safety.

**Documentation:**
- [spec/traits.md](../spec/traits.md) - Trait Coherence Rules section

### Core Coherence (#1146-1149)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #1146 | Orphan rule enforcement | ✅ | R | [traits.md](../spec/traits.md) | - | `src/compiler/tests/` |
| #1147 | Overlap detection | ✅ | R | [traits.md](../spec/traits.md) | - | `src/compiler/tests/` |
| #1148 | Associated type coherence | ✅ | R | [traits.md](../spec/traits.md) | - | `src/compiler/tests/` |
| #1149 | Blanket impl conflict detection | ✅ | R | [traits.md](../spec/traits.md) | - | `src/compiler/tests/` |

### Advanced Coherence (#1150-1153)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #1150 | Specialization (`#[default]` impl) | ✅ | R | [traits.md](../spec/traits.md) | - | `src/compiler/tests/` |
| #1151 | Negative trait bounds (`!Trait`) | ✅ | R | [traits.md](../spec/traits.md) | - | `src/compiler/tests/` |
| #1152 | Coherence error messages | ✅ | R | [traits.md](../spec/traits.md) | - | `src/compiler/tests/` |
| #1153 | Newtype pattern support | ✅ | R | [traits.md](../spec/traits.md) | - | `src/compiler/tests/` |

### Extension Methods (#1154-1155)

| Feature ID | Feature | Status | Impl | Doc | S-Test | R-Test |
|------------|---------|--------|------|-----|--------|--------|
| #1154 | Extension traits | ✅ | R | [traits.md](../spec/traits.md) | - | `src/compiler/tests/` |
| #1155 | Delegation pattern | ✅ | S | [traits.md](../spec/traits.md) | `std_lib/test/` | - |

---

## Summary

**Total Features Archived:** 57 features
**Feature Ranges:**
- Build & Linker Optimization: #800-824 (25 features)
- Module Privacy: #48-49 (2 features)
- Formatting and Lints: #1131-1145 (15 features)
- Trait Coherence: #1146-1155 (10 features)

All features marked ✅ Complete and extracted from feature.md on 2025-12-22.
