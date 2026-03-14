# Build Status After Parser Removal

**Date:** 2026-02-04
**Status:** ❌ Broken (Expected)
**Errors:** 34 compilation errors in 2 crates

## Build Results

### Bootstrap Build: ❌ FAILED
```bash
$ cargo build --profile bootstrap
error: could not compile `simple-sdn` (lib) due to 3 previous errors
error: could not compile `simple-type` (lib) due to 31 previous errors
```

### Full Release Build: ❌ FAILED
Same errors (dependency chain blocked)

## Error Summary

| Crate | Errors | Status | Blocker |
|-------|--------|--------|---------|
| `simple-sdn` | 3 | ❌ | Missing parser module |
| `simple-type` | 31 | ❌ | Missing simple_parser crate |
| `simple-compiler` | - | ⏸️ | Blocked by simple-type |
| `simple-driver` | - | ⏸️ | Blocked by simple-compiler |
| Other crates | - | ⏸️ | Blocked by dependencies |

**Total visible errors:** 34
**Total affected files:** Unknown (build stopped early)

## Error Details

### 1. simple-sdn (3 errors)

**Files affected:**
- `sdn/src/document.rs` (2 errors)
- `sdn/src/lib.rs` (1 error via parse_document function)

**Error pattern:**
```rust
error[E0432]: unresolved import `crate::parser`
 --> sdn/src/document.rs:4:12
  |
4 | use crate::parser::parse;
  |            ^^^^^^ could not find `parser` in the crate root
```

**Root cause:**
- SDN crate had `parser.rs` that depended on removed lexer
- We commented out parser module in `lib.rs`
- But `document.rs` still tries to import it

**Fix:**
- Option A: Remove SDN Rust crate (use Simple SDN parser)
- Option B: Stub out parser functions temporarily
- Option C: Create minimal SDN parser in Rust

### 2. simple-type (31 errors)

**Files affected:**
- `type/src/lib.rs`
- `type/src/effects.rs`
- `type/src/checker_check.rs`
- `type/src/checker_infer.rs`
- `type/src/macro_checker.rs`

**Error pattern:**
```rust
error[E0433]: failed to resolve: use of unresolved module or unlinked crate `simple_parser`
 --> type/src/lib.rs:1:5
  |
1 | use simple_parser::ast::{
  |     ^^^^^^^^^^^^^ use of undeclared crate or module `simple_parser`
```

**Imports needed:**
- `simple_parser::ast::*` (FunctionDef, Node, Type, Expr, Block, etc.)
- `simple_parser::ast::FStringPart`
- `simple_parser::ast::UnaryOp`
- `simple_parser::ast::AssignOp`
- `simple_parser::ast::MatchArm`
- `simple_parser::ast::MacroAnchor`
- `simple_parser::ast::MacroContractItem`
- `simple_parser::ast::EnclosingTarget`
- `simple_parser::ast::MacroDeclStub`
- `simple_parser::ast::MacroArg`

**Root cause:**
- Type checker heavily uses AST types
- All AST type definitions were in removed parser crate
- 5 files import these types extensively

**Fix needed:**
- Create AST type definitions (or FFI bridge to Simple AST)

## Dependency Chain (Why Build Stopped)

```
simple-sdn (❌ 3 errors)
simple-type (❌ 31 errors)
    ↓
simple-compiler (depends on simple-type)
    ↓
simple-driver (depends on simple-compiler)
    ↓
simple-tests (depends on simple-driver)
```

Build stops at `simple-type`, blocking all downstream crates.

## What We Know

### Crates NOT Tested Yet

These will likely have more errors once we fix simple-type:
- `simple-compiler` - ~200+ files use simple_parser
- `simple-driver` - ~40+ files use simple_parser
- `simple-test` - ~30+ files use simple_parser

**Estimated total:** 260+ files with errors (from earlier grep)

### Impact on Binary Size

Current broken state prevents any binary generation:
- Bootstrap build: N/A (can't build)
- Full release build: N/A (can't build)

## Quick Fix Options

### Option 1: Stub Out Broken Crates (Fastest - 1 hour)

Temporarily disable failing crates to test downstream:

```toml
# rust/Cargo.toml
members = [
    # "sdn",        # Disabled - needs parser
    # "type",       # Disabled - needs AST types
    "compiler",
    "driver",
    # ...
]
```

**Pros:** Can test if other crates compile
**Cons:** Type checker unavailable, compiler incomplete

### Option 2: Minimal AST Stubs (Medium - 1 day)

Create minimal Rust AST type definitions:

```rust
// rust/common/src/ast_stubs.rs
pub mod ast {
    pub struct FunctionDef;
    pub struct Node;
    pub struct Type;
    pub struct Expr;
    pub struct Block;
    pub enum FStringPart { Literal(String), Expr(Box<Expr>) }
    pub enum UnaryOp { Neg, Not, BitNot }
    pub enum AssignOp { Assign, SuspendAssign }
    // ... etc
}
```

**Pros:** Compiles, maintains type structure
**Cons:** Non-functional stubs, can't actually parse

### Option 3: FFI Bridge (Proper - 3-7 days)

Implement complete FFI bridge to Simple parser:

```simple
extern fn rt_parse_file(path: text) -> RuntimeValue
extern fn rt_parse_expr(source: text) -> RuntimeValue
```

```rust
pub fn parse_file(path: &str) -> Result<Module> {
    let value = unsafe { rt_parse_file(path) };
    runtime_value_to_module(value)
}
```

**Pros:** Full functionality, uses Simple parser
**Cons:** More work, requires serialization layer

## Recommendation

### Immediate (Today):

**Use Option 1 (Stub out crates)** to see full scope of errors:

```bash
# Temporarily disable failing crates
# rust/Cargo.toml: comment out sdn, type

# See what else breaks
cargo build --profile bootstrap 2>&1 | tee build.log
grep "error\[E" build.log | wc -l
```

### Short-term (This Week):

**Use Option 2 (Minimal stubs)** to unblock compilation:

```rust
// Create rust/common/src/ast.rs with minimal type definitions
// Update simple-type to use common::ast instead of simple_parser::ast
```

### Long-term (Next Sprint):

**Implement Option 3 (FFI bridge)** for production:

```
Week 1: FFI entry points + AST serialization
Week 2: Update 260+ Rust files
Week 3: Testing + debugging
```

## Current State Summary

✅ **Rust parser removed** - Complete
✅ **Simple parser exists** - Functional (7,400 lines)
❌ **Build broken** - 34 errors, 2 crates failing
⏸️ **Can't test further** - Dependency chain blocked

**Blocker:** Need AST type definitions or FFI bridge

## Next Steps

1. **Quick assessment:**
   ```bash
   # Comment out sdn and type in Cargo.toml
   # Try building compiler
   cargo build -p simple-compiler 2>&1 | head -100
   ```

2. **Count real impact:**
   ```bash
   # How many files actually fail?
   find rust/compiler -name "*.rs" -exec grep -l "simple_parser" {} \; | wc -l
   ```

3. **Choose approach:**
   - Need parser working? → FFI bridge (3-7 days)
   - Just need to compile? → Stubs (1 day)
   - Want to skip for now? → Disable crates (1 hour)

## Files

- **This report:** `doc/report/build_status_2026-02-04.md`
- **Pipeline:** `doc/report/pipeline_already_exists_2026-02-04.md`
- **Parser inventory:** `doc/report/simple_parser_inventory_2026-02-04.md`
- **Type conversion:** `doc/report/type_conversion_inventory_2026-02-04.md`
