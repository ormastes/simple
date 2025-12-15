# Next Session Quick Start Guide

## Current State ✅
- All 807 tests passing
- 2 bugs fixed (syntax error + backend selection)
- 4 files identified for splitting (>1000 lines each)
- Comprehensive documentation created

## What to Do Next

### Option 1: Split ast.rs (RECOMMENDED - Lowest Risk)

**Why:** Pure data structures, no logic, minimal dependencies

**Steps:**
```bash
# 1. Create directory
mkdir -p src/parser/src/ast

# 2. Create modules (copy from FILE_SPLITTING_STATUS.md)
#    - common.rs (Visibility, Mutability, etc)
#    - docs.rs (DocComment, Decorator, Attribute)
#    - definitions.rs (FunctionDef, StructDef, etc)
#    - enums.rs (EnumDef, UnitDef, etc)
#    - macros.rs (MacroDef, MacroPattern, etc)
#    - statements.rs (LetStmt, IfStmt, etc)
#    - contracts.rs (ContractBlock, etc)
#    - modules.rs (Import, Export, Use)
#    - expressions.rs (Expr enum)
#    - mod.rs (Node enum, re-exports)

# 3. Test after EACH module
cargo test -p simple-parser --lib

# 4. When done, test everything
cargo test --workspace --lib
```

**Estimated Time:** 1-2 hours  
**Risk:** Low

### Option 2: Extract Helpers from lower.rs/container.rs

**Why:** Reduces duplication before splitting

**Steps:**
```bash
# 1. Identify duplicated patterns
make duplication-simple | grep "lower.rs\|container.rs"

# 2. Extract into helper functions
#    Example: extract_common_pattern() -> Result<T>

# 3. Test after each extraction
cargo test -p simple-compiler --lib
cargo test -p simple-loader --lib

# 4. Run duplication check again
make duplication-simple
```

**Estimated Time:** 2-3 hours  
**Risk:** Medium

### Option 3: Split llvm.rs

**Why:** Well-structured, feature-gated code

**Steps:**
```bash
# 1. Create directory
mkdir -p src/compiler/src/codegen/llvm

# 2. Split into modules (see FILE_SPLITTING_STATUS.md)
#    - backend.rs
#    - types.rs
#    - module.rs
#    - codegen.rs
#    - emit.rs
#    - test_helpers.rs
#    - mod.rs

# 3. Test after EACH module
cargo test -p simple-compiler --lib

# 4. Test with llvm feature
cargo test -p simple-compiler --lib --features llvm
```

**Estimated Time:** 2-3 hours  
**Risk:** Medium

## Key Files to Reference

1. **FILE_SPLITTING_STATUS.md** - Detailed split plans
2. **DUPLICATION_REPORT.md** - Duplication analysis
3. **SESSION_SUMMARY.md** - What was done last time
4. **TASK_COMPLETION_SUMMARY.md** - Overall status

## Testing Checklist

After ANY change:
```bash
# 1. Test affected crate
cargo test -p <crate-name> --lib

# 2. Test workspace
cargo test --workspace --lib

# 3. Check duplication
make duplication-simple

# 4. Verify no files >1000 lines
find src -name "*.rs" -exec wc -l {} + | awk '$1 > 1000'
```

## Success Criteria

- ✅ All 807 tests still passing
- ✅ No files exceed 1000 lines
- ✅ Duplication reduced (fewer 51-line blocks)
- ✅ Imports updated correctly
- ✅ No breaking changes to public API

## If Something Breaks

1. **Don't panic** - you have a clean baseline
2. Run `git diff` to see what changed
3. Run `cargo test -p <crate>` to narrow down failures
4. Check imports in mod.rs files
5. Revert if needed: `git checkout -- <file>`

## Estimated Timeline

- **Phase 1 (ast.rs):** 1-2 hours
- **Phase 2 (llvm.rs):** 2-3 hours
- **Phase 3 (helpers):** 2-3 hours
- **Phase 4 (lower.rs):** 3-4 hours
- **Phase 5 (container.rs):** 3-4 hours

**Total:** 11-16 hours for complete file splitting

## Quick Commands

```bash
# Test everything
make test

# Check duplication
make duplication-simple

# Run coverage
make coverage

# Find large files
find src -name "*.rs" -exec wc -l {} + | sort -rn | head -10

# Count total tests
cargo test --workspace --lib 2>&1 | grep "test result"
```

## Tips

- Work incrementally (one module at a time)
- Test after each change
- Commit often
- Use descriptive commit messages
- Reference FILE_SPLITTING_STATUS.md for structure
- Keep terminal open with `cargo watch -x test` running

Good luck! 🚀
