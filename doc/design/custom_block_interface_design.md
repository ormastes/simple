# Custom Block User-Definable Interface Design

**Date:** 2026-01-26
**Status:** Design Draft
**Depends on:** `custom_blocks_proposal.md`, `math_block_design.md`

---

## 1. Problem Statement

Simple has built-in blocks (`m{}`, `loss{}`, `nograd{}`) with hardcoded lexer/parser support. Users cannot define their own blocks with custom syntax modes. We need a generic interface that:

1. Allows registration of custom block keywords
2. Enables lexer mode configuration per block
3. Supports custom payload parsing
4. Integrates after TreeSitter outline parsing

---

## 2. Current Architecture

### 2.1 Compilation Pipeline

```
Source Code
    ↓
┌───────────┐
│  Lexer    │ ← Hardcoded m{}/loss{}/nograd{} detection
└───────────┘
    ↓ Tokens
┌───────────┐
│ TreeSitter│ ← Fast outline (skips function bodies)
└───────────┘
    ↓ OutlineModule
┌───────────┐
│  Parser   │ ← Full AST with bodies
└───────────┘
    ↓ AST
┌───────────┐
│   HIR     │
└───────────┘
    ↓
   ...
```

### 2.2 Current Block Handling

**Lexer** (`lexer.spl:682-808`):
```simple
# Hardcoded detection
if self.peek() == 'm' and self.peek_next() == '{':
    self.in_math_block = true
    ...
if text == "loss" and lookahead == "loss{":
    self.in_math_block = true
    ...
```

**Parser** (`parser.spl:1469-1516`):
```simple
case KwLoss:
    self.parse_loss_block()
case KwNograd:
    self.parse_nograd_block()
```

**Problem**: Every new block requires lexer/parser code changes.

---

## 3. Proposed Architecture

### 3.1 New Pipeline with Block Registry

```
Source Code
    ↓
┌───────────┐
│  Lexer    │ ← Generic block detection via BlockRegistry
└───────────┘
    ↓ Tokens (with BlockStart, BlockPayload, BlockEnd)
┌───────────┐
│ TreeSitter│ ← Outline pass (blocks stored as opaque nodes)
└───────────┘
    ↓ OutlineModule (with BlockOutline nodes)
┌────────────────────┐
│ Block Resolution   │ ← NEW: Maps block kinds to handlers
└────────────────────┘
    ↓
┌───────────┐
│  Parser   │ ← Handlers parse payloads into AST
└───────────┘
    ↓ AST (with typed BlockExpr nodes)
┌───────────┐
│   HIR     │
└───────────┘
```

### 3.2 Block Registry

```simple
struct BlockRegistry:
    """Central registry for block definitions."""
    blocks: Dict<text, BlockDefinition>

impl BlockRegistry:
    static fn default() -> BlockRegistry:
        """Create registry with built-in blocks."""
        var reg = BlockRegistry(blocks: {})
        reg.register(MathBlockDef())
        reg.register(LossBlockDef())
        reg.register(NogradBlockDef())
        reg

    me register(def: BlockDefinition):
        """Register a block definition."""
        self.blocks[def.kind] = def

    fn lookup(kind: text) -> BlockDefinition?:
        """Look up block by keyword."""
        self.blocks.get(kind)

    fn is_block_keyword(word: text) -> bool:
        """Check if word is a registered block keyword."""
        self.blocks.contains_key(word)
```

### 3.3 Block Definition Interface

```simple
trait BlockDefinition:
    """Definition for a custom block type."""

    # ========================================================================
    # Required: Identity
    # ========================================================================

    fn kind() -> text:
        """Block keyword (e.g., "m", "loss", "sh", "sql")."""

    # ========================================================================
    # Required: Parsing
    # ========================================================================

    fn parse_payload(payload: text, ctx: BlockContext) -> Result<BlockValue, BlockError>:
        """Parse the block payload into a typed value.

        Args:
            payload: Raw text between { and }
            ctx: Context with source location, parent scope, etc.

        Returns:
            BlockValue containing typed AST or value
        """

    # ========================================================================
    # Optional: Lexer Mode
    # ========================================================================

    fn lexer_mode() -> LexerMode:
        """Return the lexer mode for this block's content.

        Default: LexerMode.Normal (standard Simple tokenization)
        """
        LexerMode.Normal

    # ========================================================================
    # Optional: Syntax Features
    # ========================================================================

    fn syntax_features() -> SyntaxFeatures:
        """Return enabled syntax features for this block.

        Default: No special features
        """
        SyntaxFeatures.default()

    # ========================================================================
    # Optional: IDE Support
    # ========================================================================

    fn highlight(payload: text) -> [HighlightToken]:
        """Return syntax highlighting tokens for IDE.

        Default: No highlighting (treated as plain text)
        """
        []

    fn completions(payload: text, cursor: i64) -> [Completion]:
        """Return completions at cursor position.

        Default: No completions
        """
        []

    fn hover(payload: text, cursor: i64) -> HoverInfo?:
        """Return hover information at cursor position.

        Default: No hover info
        """
        None

    # ========================================================================
    # Optional: Compile-Time Evaluation
    # ========================================================================

    fn eval_const(value: BlockValue) -> ConstValue?:
        """Evaluate block at compile time if possible.

        Default: None (runtime evaluation only)
        """
        None

    # ========================================================================
    # Optional: Code Generation
    # ========================================================================

    fn lower(value: BlockValue, ctx: LoweringContext) -> MIR:
        """Lower block value to MIR.

        Default: Generate call to runtime handler
        """
        ctx.emit_call("__block_eval__", [value.to_runtime()])
```

### 3.4 Lexer Modes

```simple
enum LexerMode:
    """Lexer mode determines tokenization behavior inside block."""

    Normal          # Standard Simple tokenization
    Math            # ^ for power, ' for transpose, implicit mul
    Raw             # Capture as raw text (no tokenization)
    Custom(config: LexerConfig)  # Custom configuration

struct LexerConfig:
    """Custom lexer configuration for blocks."""

    # Operator overrides
    caret_is_power: bool = false      # ^ as power operator
    quote_is_transpose: bool = false   # ' as postfix transpose
    implicit_mul: bool = false         # 2x → 2*x

    # String handling
    interpolation: bool = true         # Allow ${...} interpolation
    raw_strings: bool = false          # Disable escape sequences

    # Delimiter handling
    preserve_braces: bool = false      # Include {} in payload
    preserve_newlines: bool = true     # Include newlines in payload

    # Custom operators (list of (text, TokenKind) pairs)
    operators: [(text, TokenKind)] = []
```

### 3.5 Syntax Features

```simple
struct SyntaxFeatures:
    """Syntax features enabled for a block."""

    # Math-like features
    power_caret: bool = false         # ^ is power (not XOR)
    transpose_quote: bool = false      # ' is transpose (postfix)
    implicit_multiplication: bool = false  # 2x means 2*x

    # Tensor features
    broadcast_ops: bool = false        # .+ .- .* ./ .^
    matrix_mul: bool = false           # @ operator

    # ML features
    auto_backward: bool = false        # Call .backward() on result
    disable_grad: bool = false         # Disable gradient tracking

    # Shell features
    command_mode: bool = false         # Shell command syntax

    # DSL features
    custom_keywords: [text] = []       # Additional keywords

impl SyntaxFeatures:
    static fn default() -> SyntaxFeatures:
        SyntaxFeatures()

    static fn math() -> SyntaxFeatures:
        SyntaxFeatures(
            power_caret: true,
            transpose_quote: true,
            implicit_multiplication: true,
            broadcast_ops: true,
            matrix_mul: true
        )

    static fn loss() -> SyntaxFeatures:
        SyntaxFeatures.math().with_auto_backward()

    static fn nograd() -> SyntaxFeatures:
        SyntaxFeatures.math().with_disable_grad()
```

---

## 4. Built-in Block Definitions

### 4.1 Math Block

```simple
struct MathBlockDef: BlockDefinition:
    fn kind() -> text: "m"

    fn lexer_mode() -> LexerMode:
        LexerMode.Math

    fn syntax_features() -> SyntaxFeatures:
        SyntaxFeatures.math()

    fn parse_payload(payload: text, ctx: BlockContext) -> Result<BlockValue, BlockError>:
        # Parse using standard parser with math mode tokens
        val parser = Parser.new(payload)
        parser.set_mode(ParseMode.MathExpr)
        val expr = parser.parse_expr()?
        Ok(BlockValue.Expr(expr))
```

### 4.2 Loss Block

```simple
struct LossBlockDef: BlockDefinition:
    fn kind() -> text: "loss"

    fn lexer_mode() -> LexerMode:
        LexerMode.Math

    fn syntax_features() -> SyntaxFeatures:
        SyntaxFeatures.loss()

    fn parse_payload(payload: text, ctx: BlockContext) -> Result<BlockValue, BlockError>:
        val parser = Parser.new(payload)
        parser.set_mode(ParseMode.MathExpr)
        val block = parser.parse_block()?
        Ok(BlockValue.LossBlock(block))

    fn lower(value: BlockValue, ctx: LoweringContext) -> MIR:
        # Wrap in autograd context and call backward
        ctx.emit_with_autograd(value.block, auto_backward: true)
```

### 4.3 Nograd Block

```simple
struct NogradBlockDef: BlockDefinition:
    fn kind() -> text: "nograd"

    fn lexer_mode() -> LexerMode:
        LexerMode.Math

    fn syntax_features() -> SyntaxFeatures:
        SyntaxFeatures.nograd()

    fn parse_payload(payload: text, ctx: BlockContext) -> Result<BlockValue, BlockError>:
        val parser = Parser.new(payload)
        parser.set_mode(ParseMode.MathExpr)
        val block = parser.parse_block()?
        Ok(BlockValue.NogradBlock(block))

    fn lower(value: BlockValue, ctx: LoweringContext) -> MIR:
        ctx.emit_without_grad(value.block)
```

---

## 5. User-Defined Blocks

### 5.1 Registration via Module

```simple
# myblocks.spl
import compiler.blocks.{BlockDefinition, BlockRegistry}

struct JsonBlockDef: BlockDefinition:
    fn kind() -> text: "json"

    fn lexer_mode() -> LexerMode:
        LexerMode.Raw  # Don't tokenize, capture as raw text

    fn parse_payload(payload: text, ctx: BlockContext) -> Result<BlockValue, BlockError>:
        val json = parse_json(payload)?
        Ok(BlockValue.Json(json))

    fn highlight(payload: text) -> [HighlightToken]:
        json_highlighter(payload)

# In module init
blocks.register(JsonBlockDef())
```

### 5.2 Registration via Dunder Trait

```simple
# Alternative: Use __block__ trait for type-directed blocks
trait __block__<K: StaticString, R>:
    fn __block__(kind: K, payload: text) -> R

impl MyJsonType: __block__<"json", MyJsonType>:
    fn __block__(kind: "json", payload: text) -> MyJsonType:
        MyJsonType.parse(payload)

# Usage:
val config: MyJsonType = json{
    "name": "example",
    "value": 42
}
```

### 5.3 Declarative Registration

```simple
# In simple.toml or CLAUDE.md configuration
[blocks]
enabled = ["m", "loss", "nograd", "sh", "sql", "json"]

[blocks.handlers]
sh = "std.shell.ShellBlockDef"
sql = "std.sql.SqlBlockDef"
json = "mypackage.JsonBlockDef"
```

---

## 6. Integration Points

### 6.1 Lexer Integration

```simple
# In Lexer struct, add:
struct Lexer:
    ...
    block_registry: BlockRegistry
    current_block: BlockDefinition?
    block_depth: i64

# In scan_identifier(), replace hardcoded checks:
me scan_identifier() -> Token:
    ...
    val text = self.source[start:self.pos]

    # Check if identifier followed by { is a block keyword
    if self.peek() == '{':
        val block_def = self.block_registry.lookup(text)
        if block_def.?:
            # Enter block mode
            self.current_block = block_def
            self.block_depth = 0
            val mode = block_def.unwrap().lexer_mode()
            self.apply_lexer_mode(mode)
            return Token.new(TokenKind.BlockStart, span, text)

    # Normal identifier handling
    ...
```

### 6.2 TreeSitter Integration

```simple
# In TreeSitter, handle blocks as opaque nodes
struct BlockOutline:
    kind: text          # Block keyword (e.g., "m", "loss", "sh")
    payload: text       # Raw payload text
    payload_span: Span  # Span of payload for error mapping
    span: Span          # Full block span including keyword and braces

# In OutlineModule
struct OutlineModule:
    ...
    blocks: [BlockOutline]  # Top-level blocks

# In parse_outline(), detect blocks
me parse_block_outline() -> BlockOutline:
    val kind = self.current.text
    self.advance()  # Consume block keyword
    self.expect(TokenKind.LBrace)

    # Capture payload without parsing
    val payload_start = self.pos
    var depth = 1
    while depth > 0 and not self.is_at_end():
        if self.check(TokenKind.LBrace):
            depth = depth + 1
        elif self.check(TokenKind.RBrace):
            depth = depth - 1
            if depth == 0:
                break
        self.advance()

    val payload = self.source[payload_start:self.pos]
    self.expect(TokenKind.RBrace)

    BlockOutline(kind: kind, payload: payload, ...)
```

### 6.3 Block Resolution Phase (NEW)

```simple
# New phase between TreeSitter and Parser
struct BlockResolver:
    registry: BlockRegistry
    diagnostics: [Diagnostic]

impl BlockResolver:
    fn resolve(outline: OutlineModule) -> ResolvedModule:
        """Resolve all blocks in outline to their handlers."""
        var resolved_blocks: [ResolvedBlock] = []

        for block in outline.blocks:
            val def = self.registry.lookup(block.kind)
            if def.?:
                val handler = def.unwrap()
                val ctx = BlockContext(span: block.payload_span, ...)

                match handler.parse_payload(block.payload, ctx):
                    case Ok(value):
                        resolved_blocks = resolved_blocks.push(
                            ResolvedBlock(kind: block.kind, value: value, span: block.span)
                        )
                    case Err(err):
                        self.diagnostics = self.diagnostics.push(
                            Diagnostic.error(err.message, block.payload_span)
                        )
            else:
                self.diagnostics = self.diagnostics.push(
                    Diagnostic.error("Unknown block type: {block.kind}", block.span)
                )

        ResolvedModule(outline: outline, blocks: resolved_blocks)
```

### 6.4 Parser Integration

```simple
# In Parser, handle resolved blocks
me parse_primary_expr() -> Expr:
    match self.peek():
        ...
        case BlockStart:
            self.parse_block_expr()
        ...

me parse_block_expr() -> Expr:
    val kind = self.current.text
    val start = self.current.span
    self.advance()  # Consume BlockStart

    # Look up resolved block value
    val resolved = self.resolved_blocks.get(start)
    if resolved.?:
        val block = resolved.unwrap()
        self.expect(TokenKind.RBrace)  # Parser still sees closing brace
        return Expr(kind: ExprKind.Block(block.kind, block.value), span: ...)
    else:
        # Fallback: parse as regular expression
        self.error("Unresolved block")
        ...
```

---

## 7. AST Changes

### 7.1 New Expression Kind

```simple
enum ExprKind:
    ...
    # Generic block expression (replaces hardcoded LossBlock, NogradBlock)
    Block(kind: text, value: BlockValue)

enum BlockValue:
    """Typed value from block parsing."""
    Expr(expr: Expr)           # Expression result (m{})
    Block(block: Block)        # Statement block (loss{}, nograd{})
    Raw(text: text)            # Raw text (sh{}, sql{})
    Json(value: JsonValue)     # Parsed JSON
    Sql(query: SqlQuery)       # Parsed SQL
    Regex(pattern: Regex)      # Compiled regex
    Custom(data: Any)          # User-defined type
```

### 7.2 Backward Compatibility

Keep `ExprKind.LossBlock` and `ExprKind.NogradBlock` as aliases:

```simple
# For backward compatibility
fn is_loss_block(expr: Expr) -> bool:
    match expr.kind:
        case Block(kind, _) if kind == "loss": true
        case LossBlock(_): true  # Legacy
        case _: false
```

---

## 8. Implementation Plan

### Phase 1: Infrastructure (Week 1)

1. **Create BlockRegistry and BlockDefinition trait**
   - File: `simple/compiler/blocks/registry.spl`
   - File: `simple/compiler/blocks/definition.spl`

2. **Add LexerMode and SyntaxFeatures**
   - File: `simple/compiler/blocks/modes.spl`

3. **Refactor built-in blocks**
   - Create `MathBlockDef`, `LossBlockDef`, `NogradBlockDef`
   - Keep backward compatibility

### Phase 2: Lexer Integration (Week 2)

4. **Add registry to Lexer**
   - Modify `simple/compiler/lexer.spl`
   - Replace hardcoded block detection with registry lookup

5. **Add BlockStart/BlockEnd tokens**
   - Update `TokenKind` enum
   - Implement generic block tokenization

### Phase 3: TreeSitter Integration (Week 2)

6. **Add BlockOutline to TreeSitter**
   - Modify `simple/compiler/treesitter.spl`
   - Implement payload capture without parsing

7. **Create BlockResolver phase**
   - New file: `simple/compiler/blocks/resolver.spl`
   - Integrate between TreeSitter and Parser

### Phase 4: Parser Integration (Week 3)

8. **Update Parser for generic blocks**
   - Modify `simple/compiler/parser.spl`
   - Handle `ExprKind.Block` with `BlockValue`

9. **Update HIR/MIR for blocks**
   - Add block lowering support

### Phase 5: Standard Blocks (Week 4+)

10. **Implement additional standard blocks**
    - `sh{}` - Shell commands
    - `sql{}` - SQL queries
    - `re{}` - Regular expressions

11. **Documentation and tests**
    - SSpec tests for each block type
    - User documentation

---

## 9. Files to Create/Modify

| File | Action | Description |
|------|--------|-------------|
| `simple/compiler/blocks/mod.spl` | Create | Block module entry point |
| `simple/compiler/blocks/registry.spl` | Create | BlockRegistry implementation |
| `simple/compiler/blocks/definition.spl` | Create | BlockDefinition trait |
| `simple/compiler/blocks/modes.spl` | Create | LexerMode, SyntaxFeatures |
| `simple/compiler/blocks/builtin.spl` | Create | Built-in block definitions |
| `simple/compiler/blocks/resolver.spl` | Create | BlockResolver phase |
| `simple/compiler/lexer.spl` | Modify | Add registry integration |
| `simple/compiler/treesitter.spl` | Modify | Add BlockOutline |
| `simple/compiler/parser.spl` | Modify | Generic block parsing |
| `simple/compiler/hir.spl` | Modify | Block IR nodes |

---

## 10. Three-Level Block Interface (Implemented 2026-01-31)

**Status: Implemented** - Feature #1092

The BlockDefinition trait now exposes 3 levels of processing, with backward-compatible defaults:

### 10.1 New Methods on BlockDefinition

```simple
trait BlockDefinition:
    # Existing: kind(), parse_payload(), lexer_mode(), syntax_features(), ...

    # NEW Level 1: Sub-lexing
    fn lex(payload: text, pre_lex: PreLexInfo, ctx: BlockContext) -> Result<[BlockToken], BlockError>:
        Ok([])  # Default: no sub-lexing

    # NEW Level 2: Fast outline for IDE
    fn treesitter_outline(payload: text, pre_lex: PreLexInfo) -> BlockOutlineInfo:
        BlockOutlineInfo.opaque(self.kind())  # Default: opaque

    # NEW Level 3: Full parse using pre-lex info
    fn parse_full(payload: text, pre_lex: PreLexInfo, ctx: BlockContext) -> Result<BlockValue, BlockError>:
        self.parse_payload(payload, ctx)  # Default: delegates to parse_payload

    # NEW: Skip policy for TreeSitter fast mode
    fn skip_policy() -> BlockSkipPolicy:
        BlockSkipPolicy.Skippable  # Default: can skip in fast mode
```

### 10.2 New Data Types (in `blocks/modes.spl`)

| Type | Purpose |
|------|---------|
| `TextSpan` | Byte range (start, end) within payload |
| `PreLexInfo` | Pre-scan data: string_spans, comment_spans, escape_positions, brace_pairs |
| `BlockSkipPolicy` | Enum: Skippable, OutlineRequired, AlwaysFull |
| `BlockOutlineInfo` | Structural summary: kind, identifiers, external_refs, structure_kind, is_opaque |
| `BlockToken` | Sub-lexer output token |
| `BlockTokenKind` | Keyword, Identifier, Number, StringLit, Operator, Punctuation, Comment, Whitespace, Error |

### 10.3 PreLexInfo Sharing

The Rust lexer (`rust/parser/src/lexer/identifiers.rs`) now performs Tier 1+2 tracking during `scan_custom_block_payload()`:
- **Tier 1**: String spans (double/single-quoted), escape positions
- **Tier 2**: Comment spans (`#`, `--`, `/* */`), brace pair tracking

This `PreLexInfo` is stored in `TokenKind::CustomBlock` and propagated through:
1. `BlockOutline.pre_lex_info` (treesitter_types.spl)
2. `BlockContext.pre_lex_info` (context.spl)
3. `BlockResolver` passes it to `handler.parse_full()`

### 10.4 TreeSitter Fast Mode

`TreeSitter` now has `fast_mode: bool` and `apply_outline_policy()`:
- **fast_mode=true + Skippable**: Store opaque outline, skip treesitter_outline()
- **fast_mode=true + OutlineRequired**: Call treesitter_outline()
- **fast_mode=false**: Call treesitter_outline() for all blocks

### 10.5 Reference Implementation: MathBlockDef

MathBlockDef implements all 3 levels:
- `lex()`: Tokenizes into Identifier, Number, Operator, Punctuation, Whitespace
- `treesitter_outline()`: Extracts unique identifiers, skipping protected regions
- `parse_full()`: Lexes then parses tokens
- `skip_policy()`: Returns `OutlineRequired`

### 10.6 Test Coverage

5 intensive SSpec test files in `test/compiler/blocks/`:

| File | Tests | Coverage |
|------|-------|---------|
| `pre_lex_info_spec.spl` | ~60 | TextSpan, PreLexInfo predicates, edge cases |
| `block_definition_three_level_spec.spl` | ~70 | 3-level defaults, MathBlockDef all levels |
| `block_skip_policy_spec.spl` | ~20 | Policy per block, fast_mode, apply_outline_policy |
| `pre_lex_per_dsl_spec.spl` | ~35 | Per-DSL conflicts (sh/sql/re/json/m/md) |
| `block_outline_info_spec.spl` | ~40 | Outline extraction, opaque fallback |

### 10.7 Files Changed

| File | Change |
|------|--------|
| `src/compiler/blocks/modes.spl` | Added PreLexInfo, BlockOutlineInfo, BlockToken, BlockSkipPolicy, TextSpan |
| `src/compiler/blocks/definition.spl` | Added lex, treesitter_outline, parse_full, skip_policy |
| `src/compiler/blocks/context.spl` | Added pre_lex_info field |
| `src/compiler/blocks/resolver.spl` | Uses parse_full, passes PreLexInfo |
| `src/compiler/blocks/builtin_blocks_defs.spl` | MathBlockDef reference implementation |
| `src/compiler/treesitter.spl` | Added fast_mode, apply_outline_policy |
| `src/compiler/treesitter_types.spl` | Added pre_lex_info, outline_info to BlockOutline |
| `rust/parser/src/lexer/identifiers.rs` | Tier 1+2 tracking in scan_custom_block_payload |
| `rust/parser/src/token.rs` | Added PreLexInfo to CustomBlock variant |

---

## 11. Open Questions

1. **Block Nesting**: Should blocks be allowed to nest (e.g., `md{ ${graph{...}} }`)?
2. **Interpolation**: How to handle `${expr}` inside raw blocks?
3. **Error Recovery**: How to recover from malformed block payloads?
4. **Caching**: Should parsed blocks be cached for incremental compilation?
5. **Security**: How to sandbox user-defined block handlers?

---

## 12. References

- `doc/design/custom_blocks_proposal.md` - Original proposal
- `doc/design/math_block_design.md` - Math block reference
- `doc/design/lean_block_design.md` - Verification blocks
- `doc/research/custom_string_literals_2026-01-24.md` - Literal syntax comparison
