# BDD Feature Documentation - Runtime Integration Blocker

**Date:** 2025-12-29
**Status:** ⚠️ Blocked
**Blocker:** Named argument syntax not supported in Simple parser

## Summary

The BDD feature documentation system framework is complete (7 modules, 842 lines), but **runtime integration is blocked** by a missing Simple language feature: named argument syntax.

## The Blocker

### What We Need
```simple
# This syntax is REQUIRED by feature_metadata function:
feature_metadata(
    id: 1,
    name: "Lexer",
    category: "Infrastructure",
    difficulty: 3,
    status: "✅ Complete",
    impl_type: "Rust",
    spec_ref: "spec/lexer_parser.md",
    files: ["src/parser/src/lexer/mod.rs"],
    tests: ["src/parser/tests/lexer_tests.rs"]
)
```

### What Simple Parser Currently Supports
```simple
# Only positional arguments work:
some_function(1, "Lexer", "Infrastructure", 3)

# Named arguments with colons DO NOT PARSE:
some_function(id: 1, name: "Lexer")  # ❌ Parse error
```

### Error Message
```
error: compile failed: parse: Unexpected token: expected expression, found Examples
```

The parser sees `id:` and doesn't recognize it as a named parameter syntax.

## Current State

### What Works ✅
- **Framework complete**: All 7 modules implemented (~842 lines)
  - `metadata.spl` - FeatureMetadata class
  - `registry.spl` - Global registry with singleton pattern
  - `generator.spl` - Markdown template renderer
  - `index_generator.spl` - Category and master index generation
  - `file_writer.spl` - File I/O operations
  - `test_helpers.spl` - Verification utilities
  - `feature_doc.spl` - Public API

- **Tests pass**: 11 tests across 4 features (100% pass rate)

- **Module exports**: `spec/__init__.spl` correctly exports all feature_doc functions

### What's Blocked ❌
- **Calling feature_metadata()** - Can't use named argument syntax
- **Runtime integration** - Can't register metadata from tests
- **Markdown generation** - Can't call `write_feature_docs()` after tests
- **Verification** - Can't compare generated docs with baseline

## Solutions

### Option 1: Implement Named Argument Syntax (Recommended)
**Add named arguments to Simple language parser**

**Changes needed:**
1. **Parser**: `src/parser/src/expressions/mod.rs`
   - Recognize `identifier: expression` in function call arguments
   - Build AST nodes for named arguments

2. **AST**: `src/parser/src/ast.rs`
   - Add `NamedArg` variant to argument types
   - Store both positional and named arguments

3. **Interpreter**: `src/compiler/src/interpreter_call.rs`
   - Match named arguments to parameter names
   - Support mixed positional + named arguments
   - Error on unknown parameter names

**Pros:**
- Enables the designed API
- Improves language ergonomics for all functions
- Matches Python/Rust syntax conventions

**Cons:**
- Requires parser, AST, and interpreter changes
- Moderate effort (~4-8 hours)

### Option 2: Use Dict-Based Metadata (Workaround)
**Change feature_metadata to accept a Dict**

```simple
# Instead of named args, use a dict:
feature_metadata({
    "id": 1,
    "name": "Lexer",
    "category": "Infrastructure",
    "difficulty": 3,
    "status": "✅ Complete",
    "impl_type": "Rust",
    "spec_ref": "spec/lexer_parser.md",
    "files": ["src/parser/src/lexer/mod.rs"],
    "tests": ["src/parser/tests/lexer_tests.rs"]
})
```

**Changes needed:**
1. Modify `feature_doc.spl::feature_metadata` to accept `Dict[String, Any]`
2. Extract and validate keys inside the function
3. Update test files to use dict syntax

**Pros:**
- Works with current parser
- Quick fix (~1-2 hours)
- Can implement immediately

**Cons:**
- Less ergonomic API
- No type checking on keys
- Runtime errors instead of parse errors

### Option 3: Positional-Only Arguments (Not Recommended)
**Use positional arguments in strict order**

```simple
# 14 positional arguments - very error-prone:
feature_metadata(
    1,                          # id
    "Lexer",                    # name
    "Infrastructure",           # category
    3,                          # difficulty
    "✅ Complete",              # status
    "Rust",                     # impl_type
    "spec/lexer_parser.md",     # spec_ref
    ["src/parser/src/lexer/mod.rs"],  # files
    ["src/parser/tests/lexer_tests.rs"],  # tests
    "Tokenizes source code",    # description
    [],                         # examples
    [],                         # dependencies
    [2],                        # required_by
    "First stage"               # notes
)
```

**Pros:**
- Works with current parser

**Cons:**
- Extremely error-prone (14 parameters!)
- Hard to read and maintain
- Easy to get order wrong
- No optional parameters

## Recommendation

**Implement Option 1: Named Argument Syntax**

This is the right long-term solution. Named arguments are a fundamental language feature that will benefit:
- Function call clarity across all Simple code
- Optional parameter patterns
- API design flexibility
- Integration with Python-like syntax conventions

Once implemented, the BDD feature documentation system will work as designed with no workarounds needed.

## Estimated Effort

### Named Argument Implementation (Option 1)
- **Parser changes**: 2-3 hours
- **AST updates**: 1 hour
- **Interpreter integration**: 2-3 hours
- **Testing**: 1-2 hours
- **Total**: ~6-9 hours

### Dict-Based Workaround (Option 2)
- **API refactoring**: 1 hour
- **Test file updates**: 30 minutes
- **Testing**: 30 minutes
- **Total**: ~2 hours

## Next Steps

**If implementing Option 1 (Recommended):**
1. Create feature spec for named arguments (#TBD)
2. Implement parser recognition of `name: value` syntax
3. Update AST to support `NamedArg` nodes
4. Update interpreter to match named args to parameters
5. Add tests for named argument feature
6. Update feature_doc tests to use named arguments
7. Run full test suite and generate documentation

**If implementing Option 2 (Quick fix):**
1. Refactor `feature_doc.spl::feature_metadata` to accept `Dict`
2. Add key validation and extraction logic
3. Update test files to use dict syntax
4. Test and generate documentation

## Files Involved

**For Named Arguments (Option 1):**
- `src/parser/src/expressions/mod.rs` - Function call parsing
- `src/parser/src/ast.rs` - AST node definitions
- `src/compiler/src/interpreter_call.rs` - Function call execution
- `src/parser/tests/expression_tests.rs` - Parser tests

**For Dict Workaround (Option 2):**
- `simple/std_lib/src/spec/feature_doc.spl` - API change
- `simple/std_lib/test/features/all_features_spec.spl` - Test updates
- `simple/std_lib/test/features/infrastructure_spec.spl` - Test updates
- `simple/std_lib/test/features/aop_spec.spl` - Test updates
- `simple/std_lib/test/features/language_core_spec.spl` - Test updates

## Impact

**Without this fix:**
- ✅ Framework code complete and tested
- ❌ Cannot register features from tests
- ❌ Cannot generate markdown documentation
- ❌ Cannot verify against baseline
- ❌ System is non-functional for its intended purpose

**With this fix:**
- ✅ Full BDD-driven documentation generation
- ✅ Living documentation synchronized with tests
- ✅ Automated markdown file generation
- ✅ Verification against baseline
- ✅ Production-ready system

## Conclusion

The BDD feature documentation system is architecturally complete and well-designed. The only blocker is a missing language feature (named arguments) in the Simple parser. Implementing named argument syntax is the recommended path forward, as it benefits the entire language ecosystem, not just this feature.

---

**Related Reports:**
- [BDD_FEATURE_DOC_COMPLETE_2025-12-29.md](BDD_FEATURE_DOC_COMPLETE_2025-12-29.md) - Session 1 completion
- [BDD_FEATURE_DOC_INFRASTRUCTURE_2025-12-29.md](BDD_FEATURE_DOC_INFRASTRUCTURE_2025-12-29.md) - Infrastructure build

**Status:** Waiting for named argument syntax implementation
