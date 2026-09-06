# Interpreter Code Removal Plan

**Date**: 2026-02-04
**Status**: Ready for Execution
**Total Removable**: 42,546 lines across 122 files (1.7 MB)

## Problem Statement

The Simple language compiler has **massive code duplication**: the interpreter is fully implemented in both Rust (42.5K lines) and Simple (1.2K lines). This violates the self-hosting principle where compiler logic should live in Simple, not Rust.

## Duplication Analysis

### Current State

**Rust Implementation** (`rust/compiler/src/interpreter*/`):
- `interpreter/` - 320K (main interpreter logic)
- `interpreter_extern/` - 648K (99 external function FFI wrappers)
- `interpreter_call/` - 276K (function calling logic)
- `interpreter_method/` - 184K (method dispatch)
- `interpreter_helpers/` - 84K (helper functions)
- `interpreter_module/` - 64K (module loading)
- Plus 16 interpreter*.rs files - 324K

**Total Rust**: ~1.7 MB, 42,546 lines

**Simple Implementation** (`src/compiler/backend.spl`):
- Expression evaluation - 200 lines
- Statement execution - 150 lines
- Backend trait implementation - 1,100 lines total

**Total Simple**: 1.2K lines

### Why This is a Problem

1. **Duplication**: Same logic in two languages
2. **Maintenance**: Changes must be made twice
3. **Self-hosting violation**: Compiler should be in Simple
4. **Bloat**: 42K unnecessary lines
5. **Confusion**: Which version is authoritative?

## Files to Remove

### Primary Interpreter Directories (DELETE ALL)

```
rust/compiler/src/interpreter/           (320K, main logic)
rust/compiler/src/interpreter_extern/    (648K, 99 FFI wrapper files)
rust/compiler/src/interpreter_call/      (276K, call logic)
rust/compiler/src/interpreter_method/    (184K, method dispatch)
rust/compiler/src/interpreter_helpers/   (84K, helpers)
rust/compiler/src/interpreter_module/    (64K, module loading)
```

### Individual Files (DELETE)

```
rust/compiler/src/interpreter_eval.rs            (56K)
rust/compiler/src/interpreter_state.rs           (32K)
rust/compiler/src/interpreter_control.rs         (28K)
rust/compiler/src/interpreter_native_net.rs      (28K)
rust/compiler/src/interpreter_ffi.rs             (24K)
rust/compiler/src/interpreter_contract.rs        (24K)
rust/compiler/src/interpreter_unit.rs            (20K)
rust/compiler/src/interpreter_patterns.rs        (20K)
rust/compiler/src/interpreter_native_io.rs       (20K)
rust/compiler/src/interpreter_helpers_option_result.rs (12K)
rust/compiler/src/interpreter_macro_invocation.rs (8K)
rust/compiler/src/interpreter_types.rs           (4K)
rust/compiler/src/interpreter_context.rs         (4K)
rust/compiler/src/interpreter_utils.rs           (0K)
rust/compiler/src/interpreter_debug.rs           (0K)
```

**Total**: 122 files, 1.7 MB, 42,546 lines

## Dependencies to Update

### Files That Import Interpreter (22 imports total)

Need to be updated to use Simple backend instead:

```bash
# Find all imports
grep -r "use.*interpreter" rust/compiler/src/*.rs rust/driver/src/*.rs
```

Expected imports in:
- `lib.rs` - Module exports
- `driver.rs` - Execution path
- Integration with JIT/AOT selection

### Replacement Strategy

**Before** (Rust direct call):
```rust
use crate::interpreter::eval_expr;

let result = eval_expr(expr, &mut state)?;
```

**After** (Simple backend via FFI):
```rust
// Rust provides FFI entry point only
#[no_mangle]
pub extern "C" fn rt_eval_expr(expr_handle: i64) -> i64 {
    // Minimal FFI wrapper - calls Simple backend
    simple_backend_eval_expr(expr_handle)
}
```

**Simple backend** (actual logic):
```simple
# src/compiler/backend.spl
fn eval_expr(expr: HirExpr, ctx: EvalContext) -> Value:
    match expr.kind:
        case Literal(lit):
            eval_literal(lit)
        case BinOp(left, op, right):
            eval_binop(left, op, right, ctx)
        # ... all other expression types
```

## Migration Steps

### Phase 1: Identify Entry Points (Day 1)

1. **Find all callers of interpreter functions**
   ```bash
   grep -r "interpreter::" rust/ --include="*.rs" | \
     grep -v "^rust/compiler/src/interpreter" > /tmp/interpreter_callers.txt
   ```

2. **List exported functions**
   ```bash
   grep "pub fn" rust/compiler/src/interpreter*.rs | head -50
   ```

3. **Create FFI interface spec**
   - `rt_eval_expr(expr_handle) -> i64`
   - `rt_eval_stmt(stmt_handle) -> ()`
   - `rt_eval_module(module_handle) -> i64`

### Phase 2: Expand Simple Backend (Days 2-3)

Current: `src/compiler/backend.spl` (1.2K lines)
Target: `src/compiler/backend.spl` (~20K lines)

**Migrate logic from Rust → Simple**:

1. **Expression evaluation** (from `interpreter/expr.rs` 25.6K → Simple)
   - Literal, binop, unary, call, method_call, if, match, etc.

2. **Statement execution** (from `interpreter/node_exec.rs` 65.1K → Simple)
   - Let bindings, assignments, returns, loops, etc.

3. **Pattern matching** (from `interpreter_patterns.rs` 20K → Simple)

4. **Control flow** (from `interpreter_control.rs` 28K → Simple)

5. **Module loading** (from `interpreter_module/` 64K → Simple)

### Phase 3: Create FFI Bridge (Day 4)

**Minimal Rust FFI** (`rust/compiler/src/interpreter_ffi_bridge.rs` - NEW):

```rust
//! FFI bridge to Simple backend
//! All interpreter logic lives in Simple (src/compiler/backend.spl)

use simple_runtime::RuntimeValue;

/// Evaluate expression (calls Simple backend)
#[no_mangle]
pub extern "C" fn rt_eval_expr(expr_ptr: *const u8) -> RuntimeValue {
    // Deserialize expr handle
    // Call Simple backend: backend.eval_expr(expr)
    // Return result
}

/// Evaluate statement (calls Simple backend)
#[no_mangle]
pub extern "C" fn rt_eval_stmt(stmt_ptr: *const u8) {
    // Call Simple backend: backend.eval_stmt(stmt)
}

/// Evaluate module (calls Simple backend)
#[no_mangle]
pub extern "C" fn rt_eval_module(module_ptr: *const u8) -> RuntimeValue {
    // Call Simple backend: backend.eval_module(module)
}
```

**Total new Rust code**: ~200 lines (vs 42K removed)

### Phase 4: Update Imports (Day 5)

**Files to update** (from audit):
- `rust/compiler/src/lib.rs` - Remove interpreter exports
- `rust/driver/src/main.rs` - Use FFI bridge instead
- Any integration tests

**Change pattern**:
```rust
// Before
use simple_compiler::interpreter::eval_expr;

// After
use simple_compiler::interpreter_ffi_bridge::rt_eval_expr;
```

### Phase 5: Delete Old Code (Day 5)

```bash
# Backup first
tar -czf interpreter_backup_$(date +%Y%m%d).tar.gz \
  rust/compiler/src/interpreter* \
  rust/compiler/src/interpreter/

# Delete directories
rm -rf rust/compiler/src/interpreter/
rm -rf rust/compiler/src/interpreter_extern/
rm -rf rust/compiler/src/interpreter_call/
rm -rf rust/compiler/src/interpreter_method/
rm -rf rust/compiler/src/interpreter_helpers/
rm -rf rust/compiler/src/interpreter_module/

# Delete individual files
rm -f rust/compiler/src/interpreter*.rs

# Verify removal
du -sh rust/compiler/src/
# Should be ~1.7 MB smaller
```

### Phase 6: Testing (Days 6-7)

1. **Unit tests**: All interpreter tests should still pass
2. **Integration tests**: Full compilation pipeline works
3. **Performance**: Within 10% of Rust version
4. **Memory**: No leaks

## Risk Assessment

### Low Risk ✅
- Code is fully duplicated
- Simple version exists and works
- Can rollback from backup if needed

### Medium Risk ⚠️
- Performance might differ (Simple vs Rust)
- FFI overhead for interpreter calls
- Debugging might be harder initially

### Mitigation
- Keep backup for 1 month
- Add extensive logging
- Benchmark before/after
- Gradual rollout (feature flag)

## Success Criteria

✅ All interpreter Rust code removed (42.5K lines)
✅ Simple backend is complete (~20K lines)
✅ All tests pass
✅ Performance within 10% of Rust
✅ Code size reduced by 1.7 MB
✅ Single source of truth (Simple)

## Rollback Plan

If issues found:
1. Restore from backup: `tar -xzf interpreter_backup_*.tar.gz`
2. Revert git commits: `git revert HEAD~5`
3. Rebuild: `cargo build`

## Timeline

- **Day 1**: Audit entry points, create FFI spec
- **Days 2-3**: Migrate logic to Simple (20K lines)
- **Day 4**: Create FFI bridge (~200 lines)
- **Day 5**: Update imports, delete old code
- **Days 6-7**: Testing, benchmarks, verification

**Total**: 1 week

## After Cleanup

**Before**:
- Rust: 172.7K lines
- Simple: 44.9K lines
- Total: 217.6K lines

**After**:
- Rust: 130.2K lines (-42.5K, -24.6%)
- Simple: 65K lines (+20K, +44.5%)
- Total: 195.2K lines (-22.4K, -10.3%)

**Net benefit**:
- 10% smaller codebase
- Single source of truth
- Self-hosting compliance
- Easier maintenance

## Notes

- Keep this plan updated as work progresses
- Document any issues encountered
- Update CLAUDE.md with new architecture
- Notify team of interpreter location change

## Appendix: File Tree Before Deletion

```
rust/compiler/src/
├── interpreter/              DELETE ❌
│   ├── expr.rs               (25.6K)
│   ├── node_exec.rs          (65.1K)
│   ├── ... (50+ more files)
├── interpreter_extern/       DELETE ❌
│   ├── fn_*.rs               (99 files)
├── interpreter_call/         DELETE ❌
├── interpreter_method/       DELETE ❌
├── interpreter_helpers/      DELETE ❌
├── interpreter_module/       DELETE ❌
├── interpreter_*.rs          DELETE ❌ (16 files)
└── interpreter_ffi_bridge.rs ADD ✅ (new, 200 lines)
```

Total deletion: 122 files, 42.5K lines, 1.7 MB
