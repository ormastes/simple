# Folder Reorganization Progress Report - Option 3

**Date:** 2025-12-31
**Status:** Phase 1A In Progress
**Approach:** Comprehensive Reorganization + Self-Hosting Preparation

---

## COMPLETED WORK

### Phase 1A: Rust Interpreter Consolidation (80% Complete)

**Files Successfully Moved:**

✅ **Core Files** (3 files):
- `interpreter_eval.rs` → `interpreter/core/eval.rs`
- `interpreter_context.rs` → `interpreter/core/context.rs`
- `interpreter_ffi.rs` → `interpreter/core/ffi.rs`

✅ **Control Files** (1 file):
- `interpreter_control.rs` → `interpreter/control/mod.rs`

✅ **Helper Files** (3 files):
- `interpreter_helpers.rs` → `interpreter/helpers/mod.rs`
- `interpreter_helpers_option_result.rs` → `interpreter/helpers/option_result.rs`
- `interpreter_utils.rs` → `interpreter/helpers/utils.rs`

✅ **Native Integration Files** (3 files):
- `interpreter_native_io.rs` → `interpreter/native/io.rs`
- `interpreter_native_net.rs` → `interpreter/native/net.rs`
- `interpreter_extern.rs` → `interpreter/native/external.rs` (renamed to avoid keyword)

✅ **Analysis Files** (3 files):
- `interpreter_contract.rs` → `interpreter/analysis/contract.rs`
- `interpreter_types.rs` → `interpreter/analysis/types.rs`
- `interpreter_unit.rs` → `interpreter/analysis/unit.rs`

✅ **Standalone Files** (2 files):
- `interpreter_debug.rs` → `interpreter/debug.rs`
- `interpreter_module.rs` → `interpreter/module.rs`

✅ **Expression Files** (3 files):
- `interpreter_expr.rs` → `interpreter/expr/mod.rs` (1,416 lines - needs further splitting)
- `interpreter_expr_casting.rs` → `interpreter/expr/casting.rs`
- Merged `interpreter_expr/units.rs` → `interpreter/expr/units.rs`

✅ **Macro Files** (2 root files + subdirectory):
- `interpreter_macro.rs` → `interpreter/macro_handling/mod.rs`
- `interpreter_macro_invocation.rs` → `interpreter/macro_handling/invocation_old.rs` (duplicate, needs merge)
- Merged existing `interpreter_macro/` → `interpreter/macro_handling/`
  - expansion.rs, helpers.rs, hygiene.rs, invocation.rs, substitution.rs

✅ **Existing Subdirectories Merged**:
- `interpreter_call/` → `interpreter/call/` (6 files: bdd, block_execution, builtins, core, mock, mod)
- `interpreter_method/` → `interpreter/method/` (5 files: collections, primitives, special, string, mod)

✅ **Module Entry Points Created**:
- `interpreter/core/mod.rs` - exports eval, context, ffi
- `interpreter/native/mod.rs` - exports external, io, net
- `interpreter/analysis/mod.rs` - exports contract, types, unit

✅ **Main Interpreter Entry**:
- `interpreter.rs` → `interpreter/mod.rs` (needs module declarations added)

**Files Moved:** 20/20 ✅
**Subdirectories Merged:** 4/4 ✅
**New Directory Structure Created:** ✅

---

## NEW INTERPRETER STRUCTURE

```
src/compiler/src/interpreter/
├── mod.rs                          # Main entry (from interpreter.rs)
├── core/
│   ├── mod.rs                      # ✅ Created
│   ├── context.rs                  # ✅ Moved
│   ├── eval.rs                     # ✅ Moved
│   └── ffi.rs                      # ✅ Moved
├── expr/
│   ├── mod.rs                      # ✅ Moved (1,416 lines - needs splitting)
│   ├── casting.rs                  # ✅ Moved
│   └── units.rs                    # ✅ Merged
├── control/
│   └── mod.rs                      # ✅ Moved
├── macro_handling/
│   ├── mod.rs                      # ✅ Moved
│   ├── expansion.rs                # ✅ Merged
│   ├── helpers.rs                  # ✅ Merged
│   ├── hygiene.rs                  # ✅ Merged
│   ├── invocation.rs               # ✅ Merged (from subdir)
│   ├── invocation_old.rs           # ⚠️ Duplicate (needs manual merge/delete)
│   └── substitution.rs             # ✅ Merged
├── call/
│   ├── mod.rs                      # ✅ Merged
│   ├── bdd.rs                      # ✅ Merged
│   ├── block_execution.rs          # ✅ Merged
│   ├── builtins.rs                 # ✅ Merged
│   ├── core.rs                     # ✅ Merged
│   └── mock.rs                     # ✅ Merged
├── method/
│   ├── mod.rs                      # ✅ Merged
│   ├── collections.rs              # ✅ Merged
│   ├── primitives.rs               # ✅ Merged
│   ├── special.rs                  # ✅ Merged
│   └── string.rs                   # ✅ Merged
├── helpers/
│   ├── mod.rs                      # ✅ Moved
│   ├── option_result.rs            # ✅ Moved
│   └── utils.rs                    # ✅ Moved
├── native/
│   ├── mod.rs                      # ✅ Created
│   ├── external.rs                 # ✅ Moved (renamed from extern.rs)
│   ├── io.rs                       # ✅ Moved
│   └── net.rs                      # ✅ Moved
├── analysis/
│   ├── mod.rs                      # ✅ Created
│   ├── contract.rs                 # ✅ Moved
│   ├── types.rs                    # ✅ Moved
│   └── unit.rs                     # ✅ Moved
├── debug.rs                        # ✅ Moved
└── module.rs                       # ✅ Moved
```

---

## REMAINING WORK

### Immediate (Phase 1A Completion - 20% remaining)

**1. Update `interpreter/mod.rs` Module Declarations**

Add at the top of the file (after imports):
```rust
// Submodules
pub mod analysis;
pub mod call;
pub mod control;
pub mod core;
pub mod debug;
pub mod expr;
pub mod helpers;
pub mod macro_handling;
pub mod method;
pub mod module;
pub mod native;

// Re-exports for backward compatibility
pub use analysis::*;
pub use call::*;
pub use control::*;
pub use core::*;
pub use expr::*;
pub use helpers::*;
pub use macro_handling::*;
pub use method::*;
pub use native::*;
```

**2. Fix Internal References in `interpreter/mod.rs`**

Find and replace:
- `crate::interpreter_unit::*` → `crate::interpreter::analysis::unit::*` OR `self::analysis::unit::*`

**3. Update `src/compiler/src/lib.rs`**

Change:
```rust
// OLD
pub mod interpreter;
pub mod interpreter_call;
pub mod interpreter_expr;
pub mod interpreter_macro;
pub mod interpreter_method;
pub use interpreter::*;

// NEW
pub mod interpreter;
pub use interpreter::*;
```

Remove declarations:
- `pub mod interpreter_call;`
- `pub mod interpreter_expr;`
- `pub mod interpreter_macro;`
- `pub mod interpreter_method;`

**4. Update All Import Statements Across Codebase**

Files that likely import interpreter modules (needs global search/replace):

Search patterns to replace:
```rust
// Pattern 1: Direct module imports
use crate::interpreter_call:: → use crate::interpreter::call::
use crate::interpreter_expr:: → use crate::interpreter::expr::
use crate::interpreter_macro:: → use crate::interpreter::macro_handling::
use crate::interpreter_method:: → use crate::interpreter::method::

// Pattern 2: Crate-level imports (from lib.rs pub use)
use simple_compiler::interpreter_call:: → use simple_compiler::interpreter::call::
use simple_compiler::interpreter_expr:: → use simple_compiler::interpreter::expr::
// ... etc

// Pattern 3: Relative imports within compiler crate
use super::interpreter_call:: → use super::interpreter::call::
```

Estimated files affected: **50-100 files** (need to grep the entire codebase)

**5. Remove Old Empty Directories**

```bash
rm -rf src/compiler/src/interpreter_call/
rm -rf src/compiler/src/interpreter_expr/
rm -rf src/compiler/src/interpreter_macro/
rm -rf src/compiler/src/interpreter_method/
```

**6. Resolve Duplicate Files**

Check if `interpreter/macro_handling/invocation_old.rs` and `invocation.rs` are duplicates:
- If identical: delete `invocation_old.rs`
- If different: manually merge or decide which to keep

**7. Test Compilation**

```bash
cargo build -p simple-compiler
```

Fix any remaining import errors.

---

### Phase 1B: Split Large Files (Pending)

**interpreter/expr/mod.rs (1,416 lines)** → Split into:
- `mod.rs` - Main dispatch (200 lines)
- `literals.rs` - Int, Float, String, Bool, None (150 lines)
- `arithmetic.rs` - BinOp: +, -, *, /, %, ** (200 lines)
- `comparison.rs` - BinOp: ==, !=, <, >, <=, >= (150 lines)
- `logical.rs` - BinOp: and, or, UnaryOp: not (100 lines)
- `collections.rs` - Array, Tuple, Dict, Set literals (250 lines)
- `indexing.rs` - Index, slice operations (200 lines)
- `comprehensions.rs` - List/dict/set comprehensions (100 lines)
- `calls.rs` - Function calls, method calls (200 lines)

Total: ~1,550 lines (accounts for mod.rs overhead)

### Phase 1C: Archive Legacy Code (Pending)

```bash
mkdir -p archive/legacy_2024/
mv lib/std/ archive/legacy_2024/stdlib_old/
mv test/ archive/legacy_2024/test_old/
```

Update `CLAUDE.md` to remove references.

---

## MIGRATION SCRIPT

### Automated Import Update Script

```bash
#!/bin/bash
# File: scripts/update_interpreter_imports.sh

echo "Updating interpreter imports across codebase..."

# Find all Rust files
find src/ tests/ -name "*.rs" -type f | while read file; do
  # Skip files in the interpreter directory itself
  if [[ "$file" == *"interpreter/"* ]]; then
    continue
  fi

  # Pattern 1: Direct crate imports
  sed -i 's/use crate::interpreter_call::/use crate::interpreter::call::/g' "$file"
  sed -i 's/use crate::interpreter_expr::/use crate::interpreter::expr::/g' "$file"
  sed -i 's/use crate::interpreter_macro::/use crate::interpreter::macro_handling::/g' "$file"
  sed -i 's/use crate::interpreter_method::/use crate::interpreter::method::/g' "$file"

  # Pattern 2: Crate-level imports
  sed -i 's/use simple_compiler::interpreter_call::/use simple_compiler::interpreter::call::/g' "$file"
  sed -i 's/use simple_compiler::interpreter_expr::/use simple_compiler::interpreter::expr::/g' "$file"
  sed -i 's/use simple_compiler::interpreter_macro::/use simple_compiler::interpreter::macro_handling::/g' "$file"
  sed -i 's/use simple_compiler::interpreter_method::/use simple_compiler::interpreter::method::/g' "$file"

  # Pattern 3: Relative imports
  sed -i 's/use super::interpreter_call::/use super::interpreter::call::/g' "$file"
  sed -i 's/use super::interpreter_expr::/use super::interpreter::expr::/g' "$file"
  sed -i 's/use super::interpreter_macro::/use super::interpreter::macro_handling::/g' "$file"
  sed -i 's/use super::interpreter_method::/use super::interpreter::method::/g' "$file"
done

echo "Import updates complete. Run 'cargo build' to verify."
```

Make executable and run:
```bash
chmod +x scripts/update_interpreter_imports.sh
./scripts/update_interpreter_imports.sh
```

---

## VERIFICATION CHECKLIST

### Phase 1A Completion Checklist

- [x] All 20 interpreter files moved
- [x] 4 subdirectories merged
- [x] New mod.rs files created for core/, native/, analysis/
- [ ] interpreter/mod.rs module declarations added
- [ ] Internal references in interpreter/mod.rs fixed
- [ ] src/compiler/src/lib.rs updated
- [ ] Import statements updated across codebase (use script)
- [ ] Old empty directories removed
- [ ] Duplicate invocation files resolved
- [ ] Compilation successful: `cargo build -p simple-compiler`
- [ ] Tests passing: `cargo test -p simple-compiler`

---

## NEXT PHASES SUMMARY

**Phase 1B:** Split interpreter/expr/mod.rs (1,416 lines → 9 files)
**Phase 1C:** Archive legacy code (lib/std/, test/)
**Phase 2A:** Split regenerate.spl (2,555 lines)
**Phase 2B:** Split and extract fs.spl common base
**Phase 2C:** Split tensor_class.spl (871 lines)
**Phase 3A:** Reorganize compiler crate (65→15 modules)
**Phase 3B:** Rename test/ → tests/
**Phase 4:** Split compiler into 6 crates
**Phase 5:** Create Simple interpreter
**Phase 6:** Documentation restructuring
**Phase 7:** Final testing and reporting

---

## RECOMMENDATIONS

**To complete Phase 1A:**

1. **Run the migration script** to update all imports automatically
2. **Manually update** `interpreter/mod.rs` and `lib.rs` as detailed above
3. **Test compilation:** `cargo build -p simple-compiler`
4. **Fix any remaining import errors** (likely 5-10 files)
5. **Run tests:** `cargo test -p simple-compiler`
6. **Commit changes:** `jj describe -m "Phase 1A: Consolidate interpreter code into interpreter/ directory"`

**Estimated time to complete Phase 1A:** 1-2 hours (mostly automated via script)

**To proceed with full Option 3:** After Phase 1A is complete and tested, proceed systematically through remaining phases. Total estimated time: 20-30 hours.

---

## STATUS SUMMARY

- **Phase 1A:** 80% complete (file moves done, imports need updating)
- **Remaining:** Phases 1B through 7 (19 major tasks)
- **Current state:** Compilable after import updates
- **Risk level:** Low (changes are mechanical and reversible)

Next action: Run migration script and complete Phase 1A checklist.
