# Lexer Desugaring Example: Full → Core

**File:** `src/compiler/lexer.spl` → `src/compiler_core/lexer.spl`  
**Size:** 1,430 lines  
**Date:** 2026-02-10

This document shows a concrete example of transforming Full Simple to Core Simple, using the lexer as a case study.

---

## Transformation 1: Remove `impl` Block

### Before (Full Simple):
```simple
struct Lexer:
    source: text
    pos: i64
    line: i64

impl Lexer:
    static fn new(source: text) -> Lexer:
        Lexer(
            source: source,
            pos: 0,
            line: 1
        )
    
    me next() -> Token:
        # Implementation...
        pass
    
    me current_char() -> text:
        if self.pos >= self.source.len():
            return ""
        self.source[self.pos:self.pos + 1]
```

### After (Core Simple):
```simple
struct Lexer:
    source: text
    pos: i64
    line: i64

# Static method → module function
fn lexer_new(source: text) -> Lexer:
    Lexer(
        source: source,
        pos: 0,
        line: 1
    )

# Instance method → function with self parameter
fn lexer_next(self: Lexer) -> Token:
    # Implementation...
    pass

fn lexer_current_char(self: Lexer) -> text:
    if self.pos >= self.source.len():
        return ""
    self.source[self.pos:self.pos + 1]
```

**Call sites:**
```simple
# Before: obj.method()
val lexer = Lexer.new(source)
val token = lexer.next()
val ch = lexer.current_char()

# After: module_function(obj)
val lexer: Lexer = lexer_new(source)
val token: Token = lexer_next(lexer)
val ch: text = lexer_current_char(lexer)
```

---

## Transformation 2: Desugar `Option<T>`

### Before (Full Simple):
```simple
struct Lexer:
    pending_token: Token?
    block_registry: BlockRegistry?
    current_block_kind: text?
    unified_registry: UnifiedRegistry?

me get_block_registry() -> BlockRegistry:
    if not self.block_registry.?:
        use blocks.{block_registry}
        self.block_registry = Some(block_registry())
    self.block_registry.unwrap()

me next() -> Token:
    if self.pending_token.?:
        val token = self.pending_token.unwrap()
        self.pending_token = nil
        return token
    # ...
```

### After (Core Simple):
```simple
struct Lexer:
    # Option<Token> → has_pending + token value
    has_pending_token: bool
    pending_token_value: Token
    
    # Option<BlockRegistry> → has_registry + registry value
    has_block_registry: bool
    block_registry_value: BlockRegistry
    
    # Option<text> → has_kind + kind value
    has_current_block_kind: bool
    current_block_kind_value: text
    
    # Option<UnifiedRegistry> → has_unified + unified value
    has_unified_registry: bool
    unified_registry_value: UnifiedRegistry

fn lexer_get_block_registry(self: Lexer) -> BlockRegistry:
    if not self.has_block_registry:
        use blocks.{block_registry}
        self.has_block_registry = true
        self.block_registry_value = block_registry()
    self.block_registry_value

fn lexer_next(self: Lexer) -> Token:
    if self.has_pending_token:
        val token: Token = self.pending_token_value
        self.has_pending_token = false
        # Clear value (optional, for GC)
        self.pending_token_value = token_eof()
        return token
    # ...
```

**Pattern:**
- `field: T?` → `has_field: bool, field_value: T`
- `Some(value)` → `has_field = true, field_value = value`
- `nil` → `has_field = false`
- `.?` operator → Check `has_field`
- `.unwrap()` → Access `field_value`

---

## Transformation 3: Desugar Pattern Matching

### Before (Full Simple):
```simple
me maybe_insert_implicit_mul(token: Token) -> Token:
    if not self.in_math_block:
        self.prev_token_kind = token.kind
        return token

    val needs_implicit_mul = match (self.prev_token_kind, token.kind):
        # number followed by identifier: 2x
        case (IntLit, Ident) | (FloatLit, Ident): true
        # number followed by lparen: 2(x+1)
        case (IntLit, LParen) | (FloatLit, LParen): true
        # rparen followed by identifier: (x+1)y
        case (RParen, Ident): true
        # rparen followed by lparen: (a)(b)
        case (RParen, LParen): true
        # identifier followed by lparen could be function call
        case _: false
    
    if needs_implicit_mul:
        # Store current token
        self.pending_token = Some(token)
        # Return ImplicitMul token
        return Token.new(TokenKind.ImplicitMul, ...)
    
    self.prev_token_kind = token.kind
    token
```

### After (Core Simple):
```simple
fn lexer_maybe_insert_implicit_mul(self: Lexer, token: Token) -> Token:
    if not self.in_math_block:
        self.prev_token_kind = token.kind
        return token

    # Pattern match → if-else chain
    var needs_implicit_mul: bool = false
    
    # (IntLit, Ident) | (FloatLit, Ident)
    val is_int_lit: bool = self.prev_token_kind == TOK_INT_LIT
    val is_float_lit: bool = self.prev_token_kind == TOK_FLOAT_LIT
    val is_num_lit: bool = is_int_lit or is_float_lit
    val is_ident: bool = token.kind == TOK_IDENT
    if is_num_lit and is_ident:
        needs_implicit_mul = true
    
    # (IntLit, LParen) | (FloatLit, LParen)
    val is_lparen: bool = token.kind == TOK_LPAREN
    if is_num_lit and is_lparen:
        needs_implicit_mul = true
    
    # (RParen, Ident)
    val is_rparen: bool = self.prev_token_kind == TOK_RPAREN
    if is_rparen and is_ident:
        needs_implicit_mul = true
    
    # (RParen, LParen)
    if is_rparen and is_lparen:
        needs_implicit_mul = true
    
    if needs_implicit_mul:
        # Store current token
        self.has_pending_token = true
        self.pending_token_value = token
        # Return ImplicitMul token
        return token_new(TOK_IMPLICIT_MUL, ...)
    
    self.prev_token_kind = token.kind
    token
```

**Pattern:**
- `match expr: case pattern: value` → Nested if-else
- Tuple matching `(a, b)` → Separate variable comparisons
- `|` (or patterns) → Logical OR
- `_` wildcard → Final else

---

## Transformation 4: Enum with Payloads

### Before (Full Simple):
```simple
enum TokenKind:
    IntLit
    FloatLit
    StringLit
    Ident
    Error(text)  # Payload: error message
    Eof

struct Token:
    kind: TokenKind
    span: Span
    text: text

fn make_error_token(msg: text, span: Span) -> Token:
    Token(
        kind: TokenKind.Error(msg),
        span: span,
        text: ""
    )
```

### After (Core Simple):
```simple
# Enum without payloads → integer tags
val TOK_INT_LIT: i64 = 0
val TOK_FLOAT_LIT: i64 = 1
val TOK_STRING_LIT: i64 = 2
val TOK_IDENT: i64 = 3
val TOK_ERROR: i64 = 4
val TOK_EOF: i64 = 5

struct Token:
    kind: i64           # Token kind tag
    span: Span
    text: text
    error_msg: text     # Payload for TOK_ERROR

fn make_error_token(msg: text, span: Span) -> Token:
    Token(
        kind: TOK_ERROR,
        span: span,
        text: "",
        error_msg: msg
    )
```

**Pattern:**
- Enum variants → Integer constants
- Payload `Error(text)` → Separate field `error_msg: text`
- Pattern matching on enum → if-else on integer tags

---

## Transformation 5: Remove Tree-sitter Dependency

### Before (Full Simple):
```simple
use treesitter.*
use blocks.*

impl Lexer:
    me parse_outline() -> Outline:
        val ts = TreeSitter.new(self.source)
        val outline = ts.parse_outline()
        outline
```

### After (Core Simple):
```simple
# Remove tree-sitter import
use core.parser.*

fn lexer_parse_outline(self: Lexer) -> Outline:
    # Use direct token-based parsing instead
    lex_init(self.source)
    parse_module()
```

**Alternative:** If tree-sitter is essential, keep as WFFI external library.

---

## Transformation 6: Method Chaining

### Before (Full Simple):
```simple
val result = source
    .trim()
    .split("\n")
    .filter(|line| not line.is_empty())
    .map(|line| line.to_uppercase())
```

### After (Core Simple):
```simple
val trimmed: text = text_trim(source)
val lines: [text] = text_split(trimmed, "\n")
val non_empty: [text] = array_filter_non_empty(lines)
val uppercase: [text] = array_map_uppercase(non_empty)
val result: [text] = uppercase

# Helper functions
fn array_filter_non_empty(arr: [text]) -> [text]:
    var result: [text] = []
    var i: i64 = 0
    while i < arr.len():
        val line: text = arr[i]
        if not text_is_empty(line):
            result = result.push(line)
        i = i + 1
    result

fn array_map_uppercase(arr: [text]) -> [text]:
    var result: [text] = []
    var i: i64 = 0
    while i < arr.len():
        val line: text = arr[i]
        result = result.push(text_to_uppercase(line))
        i = i + 1
    result
```

---

## Transformation 7: Generic Types Used

### Full Simple Types:
```simple
struct Lexer:
    pending_token: Token?
    block_registry: BlockRegistry?
```

### Core Simple Replacements:

**Option 1: Monomorphization**
```simple
struct OptionToken:
    is_some: bool
    value: Token

struct OptionBlockRegistry:
    is_some: bool
    value: BlockRegistry
```

**Option 2: Tagged Union (Simpler)**
```simple
struct Lexer:
    has_pending_token: bool
    pending_token_value: Token
    has_block_registry: bool
    block_registry_value: BlockRegistry
```

We use **Option 2** because it's simpler and doesn't require creating new types.

---

## Full File Transformation Summary

### Changes Required for `lexer.spl`:

1. ✅ **Remove `impl Lexer:`** → Convert 30+ methods to module functions
   - `static fn new()` → `fn lexer_new()`
   - `me next()` → `fn lexer_next(self: Lexer)`
   - ~30 method conversions total

2. ✅ **Desugar Option Types** (4 fields):
   - `pending_token: Token?`
   - `block_registry: BlockRegistry?`
   - `current_block_kind: text?`
   - `unified_registry: UnifiedRegistry?`

3. ✅ **Desugar Pattern Matching** (~5 match expressions)

4. ✅ **Remove Tree-sitter** (if possible)
   - OR keep as WFFI library

5. ✅ **Update Call Sites** (all usage of lexer in other files)

### Estimated Effort:

- **Manual conversion:** 4-6 hours for experienced developer
- **Automated tool:** 1-2 hours to implement + 30 minutes to run
- **Testing:** 2-3 hours to verify correctness

### Lines Changed:

- Original: 1,430 lines
- Expected: ~1,600 lines (slightly more verbose without syntactic sugar)
- Core-compatible: Yes

---

## Verification Steps

1. ✅ **Compile with seed:**
   ```bash
   seed_cpp src/compiler_core/lexer.spl --output build/lexer.cpp
   ```

2. ✅ **Run lexer tests:**
   ```bash
   simple test test/unit/compiler/lexer_spec.spl
   ```

3. ✅ **Integration test:**
   ```bash
   # Use desugared lexer in parser
   simple src/main.spl --use-core-lexer
   ```

4. ✅ **Bootstrap test:**
   ```bash
   # Full compiler uses desugared lexer
   simple build --bootstrap
   ```

---

## Next Steps

1. **Manual conversion:** Create `src/compiler_core/lexer.spl`
2. **Test compilation:** Verify it compiles with seed
3. **Document patterns:** Note all transformation rules
4. **Automate:** Implement desugarer tool
5. **Expand:** Apply to remaining 51 files in `src/compiler/`

---

## Automation Opportunities

### High Priority (Easy wins):
- ✅ `impl` block removal (mechanical)
- ✅ Method call → Function call (straightforward)
- ✅ Option type desugaring (pattern-based)

### Medium Priority:
- ✅ Pattern matching → if-else (requires careful logic)
- ✅ Closure lifting (need to track captures)

### Low Priority (Complex):
- ❌ Tree-sitter removal (may need manual intervention)
- ❌ Generic monomorphization (type analysis required)

---

**End of Example**
