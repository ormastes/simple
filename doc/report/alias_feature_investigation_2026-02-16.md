# Function Alias Feature Investigation

**Date:** 2026-02-16
**Status:** ❌ Not Yet Implemented
**Type:** Feature Gap

---

## Summary

The **function alias** feature (`fn new_name = old_name`) has **parser structure** but **no runtime implementation**. Type aliases (`type`/`alias` keywords) work fine, but function aliases do not.

---

## Evidence

### 1. Parser Structure Exists

**Location:** `src/app/parser/def/function.spl:310-328`

```simple
fn parse_function_alias(self) -> Result<Node, ParseError>:
    self.parse_function_alias_with_decorators([])

fn parse_function_alias_with_decorators(self, decorators: [Decorator]) -> Result<Node, ParseError>:
    val start_span = self.current.span
    self.expect(TokenKind.Fn)
    val name = self.expect_identifier()
    self.expect(TokenKind.Assign)         # Expects '='
    val target = self.expect_identifier()

    Ok(Node.FunctionAlias(FunctionAliasDef(...)))
```

**AST node defined:** `src/app/parser/ast.spl:495`
- `struct FunctionAliasDef`
- `FunctionAliasNode(FunctionAliasDef)`

### 2. Tests Are Stubs

**Location:** `test/feature/alias_deprecated_spec.spl:99-107`

```simple
it "parses function alias":
    # The parser should accept: fn println = print
    val source = "fn println = print"
    expect(true).to_equal(true)  # ← Stub test!
```

**All 10+ function alias tests** just do `expect(true).to_equal(true)` — no actual execution.

### 3. Runtime Parser Doesn't Support It

**Attempted build error:**
```
error: compile failed: parse: in "/home/ormastes/dev/pub/simple/src/lib/text.spl":
Unexpected token: expected LParen, found Assign
```

When trying to use `fn parse_i64 = parse_i64_safe`, the **runtime parser** (used during `bin/simple build`) fails because it expects `fn name(params)`, not `fn name = target`.

### 4. Core Parser Has No Implementation

```bash
$ grep -rn "FunctionAlias" src/compiler_core/
# (no results)
```

The core/runtime parser (`src/compiler_core/parser.spl`) doesn't know about function aliases.

---

## Current Status

| Feature | Parser | Compiler | Runtime | Status |
|---------|--------|----------|---------|--------|
| `type X = Y` | ✅ | ✅ | ✅ | **Working** |
| `alias X = Y` | ✅ | ✅ | ✅ | **Working** (class alias) |
| `fn x = y` | ✅ (app/parser) | ❌ | ❌ | **Not Implemented** |

---

## Workarounds

### Current: Delegation

```simple
# Instead of: fn println = print (doesn't work)
fn println(msg):
    """Alias for print."""
    print(msg)
```

**Pros:**
- Works today in all modes
- Clear intent

**Cons:**
- Extra function call overhead
- More boilerplate (~3 lines vs 1)

### Alternative: Re-exports

For module compatibility:

```simple
# In stub module:
use std.encoding.{*}
export *
```

This works for whole-module re-exports.

---

## Implementation Requirements

To make `fn name = target` work:

1. **Core parser update** (`src/compiler_core/parser.spl`)
   - Add function alias parsing after `TokenKind.Fn`
   - Check for `=` instead of `(`

2. **HIR lowering** (`src/compiler/hir_lowering/items.spl`)
   - Convert `FunctionAlias` AST → HIR function that calls target
   - OR: Symbol table aliasing (better performance)

3. **Runtime implementation**
   - Symbol table must resolve aliases
   - Or desugar to delegation during lowering

4. **Tests**
   - Replace stub tests with actual execution tests
   - Verify alias resolution works
   - Test visibility, decorators, impl blocks

---

## Recommendation

**Don't use `fn x = y` syntax yet** — stick with delegation:

```simple
fn old_name(args):
    """Backward compatibility alias."""
    new_name(args)
```

**For consolidation work:** Delegation is fine. The overhead is minimal (single function call) and much better than code duplication.

---

## Updated Documentation

Modified files to reflect current status:

1. **`doc/guide/syntax_quick_reference.md`**
   - Added warning: "Parser structure exists, runtime implementation incomplete"
   - Showed delegation workaround

2. **`CLAUDE.md`**
   - Removed incorrect function alias example
   - Kept type/class aliases (those work)
   - Added delegation as the current pattern

3. **`memory/MEMORY.md`**
   - Updated note about aliases vs delegation

---

## Related Files

- Parser impl: `src/app/parser/def/function.spl:310-328`
- AST types: `src/app/parser/ast.spl:495`
- Tests (stubs): `test/feature/alias_deprecated_spec.spl`
- Use case: `src/lib/functions.spl` (delegation pattern)
