# Custom Block Interface - Implementation Plan

**Date:** 2026-01-26
**Design Doc:** `custom_block_interface_design.md`
**Priority:** High (enables user extensibility)

---

## Overview

Implement a user-definable custom block interface that integrates after TreeSitter parsing. This allows users to define blocks like `sh{}`, `sql{}`, `json{}` with custom lexer modes and parsing.

---

## Phase 1: Core Infrastructure

### Task 1.1: Create Block Module Structure

**Files to create:**
```
simple/compiler/blocks/
├── mod.spl           # Module entry point
├── registry.spl      # BlockRegistry implementation
├── definition.spl    # BlockDefinition trait
├── modes.spl         # LexerMode, SyntaxFeatures
├── context.spl       # BlockContext, BlockError
├── value.spl         # BlockValue enum
└── builtin/
    ├── mod.spl       # Built-in blocks entry
    ├── math.spl      # MathBlockDef
    ├── loss.spl      # LossBlockDef
    └── nograd.spl    # NogradBlockDef
```

**Deliverables:**
- [ ] `BlockDefinition` trait with all methods
- [ ] `BlockRegistry` with registration/lookup
- [ ] `LexerMode` enum and `LexerConfig` struct
- [ ] `SyntaxFeatures` struct with presets
- [ ] `BlockContext` and `BlockError` types
- [ ] `BlockValue` enum for parsed results

### Task 1.2: Refactor Built-in Blocks

**Goal:** Move hardcoded `m{}`, `loss{}`, `nograd{}` to use new interface.

**Changes:**
1. Create `MathBlockDef`, `LossBlockDef`, `NogradBlockDef` implementing `BlockDefinition`
2. Register them in default `BlockRegistry`
3. Verify backward compatibility

**Acceptance Criteria:**
- [ ] Existing tests pass unchanged
- [ ] `m{}` still works with ^, ', implicit mul
- [ ] `loss{}` still enables autograd + auto-backward
- [ ] `nograd{}` still disables gradients

---

## Phase 2: Lexer Integration

### Task 2.1: Add Block Tokens

**File:** `simple/compiler/lexer.spl`

**New TokenKind variants:**
```simple
enum TokenKind:
    ...
    BlockStart(kind: text)  # Block keyword detected
    BlockPayload(text: text) # Raw payload text (for Raw mode)
    BlockEnd               # Closing brace of block
```

### Task 2.2: Registry-Based Block Detection

**Current (hardcoded):**
```simple
if self.peek() == 'm' and self.peek_next() == '{':
    self.in_math_block = true
```

**New (registry-based):**
```simple
# In Lexer struct
block_registry: BlockRegistry
current_block_def: BlockDefinition?
block_mode: LexerMode

# In scan_identifier()
if self.peek() == '{':
    val def = self.block_registry.lookup(text)
    if def.?:
        self.enter_block(def.unwrap())
        return Token.new(TokenKind.BlockStart(text), span, text)
```

### Task 2.3: Mode-Based Tokenization

**Implement `apply_lexer_mode(mode: LexerMode)`:**

```simple
me apply_lexer_mode(mode: LexerMode):
    match mode:
        case LexerMode.Normal:
            self.reset_special_modes()
        case LexerMode.Math:
            self.in_math_block = true
            # Already implemented
        case LexerMode.Raw:
            self.in_raw_block = true
            # Capture everything until balanced }
        case LexerMode.Custom(config):
            self.apply_custom_config(config)
```

### Task 2.4: Raw Mode Implementation

**For blocks like `sh{}`, `sql{}` that don't tokenize content:**

```simple
me scan_raw_block_payload() -> Token:
    """Capture raw text until balanced closing brace."""
    val start = self.pos
    var depth = 1

    while depth > 0 and not self.is_at_end():
        val c = self.advance()
        if c == '{':
            depth = depth + 1
        elif c == '}':
            depth = depth - 1

    val payload = self.source[start:self.pos - 1]  # Exclude closing }
    Token.new(TokenKind.BlockPayload, Span.new(start, self.pos - 1, ...), payload)
```

---

## Phase 3: TreeSitter Integration

### Task 3.1: Add BlockOutline

**File:** `simple/compiler/treesitter.spl`

```simple
struct BlockOutline:
    """Outline for a block expression."""
    kind: text              # Block keyword
    payload: text           # Raw payload text
    payload_span: Span      # For error mapping
    span: Span              # Full span

struct OutlineModule:
    ...
    inline_blocks: [BlockOutline]  # Blocks in expressions
```

### Task 3.2: Block Capture in Outline

**Add to TreeSitter:**

```simple
me parse_block_outline() -> BlockOutline:
    """Capture block without parsing payload."""
    val kind = self.current.text
    val start = self.current.span
    self.advance()  # Consume keyword

    # Expect {
    if not self.match_token(TokenKind.LBrace):
        if self.match_token(TokenKind.BlockStart):
            # Already consumed by lexer
            pass
        else:
            self.error("Expected '{' after block keyword")

    # Capture payload
    val payload_start = self.pos
    self.skip_block_content()
    val payload_end = self.pos

    val payload = self.source[payload_start:payload_end]

    BlockOutline(
        kind: kind,
        payload: payload,
        payload_span: Span.new(payload_start, payload_end, ...),
        span: start.merge(self.previous.span)
    )
```

---

## Phase 4: Block Resolution Phase

### Task 4.1: Create BlockResolver

**New file:** `simple/compiler/blocks/resolver.spl`

```simple
struct BlockResolver:
    """Resolves blocks from outline to typed values."""
    registry: BlockRegistry
    diagnostics: [Diagnostic]

struct ResolvedBlock:
    kind: text
    value: BlockValue
    span: Span
    payload_span: Span

impl BlockResolver:
    fn resolve_module(outline: OutlineModule) -> (ResolvedModule, [Diagnostic]):
        var resolver = BlockResolver(
            registry: BlockRegistry.default(),
            diagnostics: []
        )

        var resolved: [ResolvedBlock] = []
        for block in outline.inline_blocks:
            match resolver.resolve_block(block):
                case Ok(rb): resolved = resolved.push(rb)
                case Err(e): pass  # Error already recorded

        (ResolvedModule(outline: outline, blocks: resolved), resolver.diagnostics)

    me resolve_block(block: BlockOutline) -> Result<ResolvedBlock, ()>:
        val def = self.registry.lookup(block.kind)
        if not def.?:
            self.diagnostics = self.diagnostics.push(
                Diagnostic.error("Unknown block type: '{block.kind}'", block.span)
            )
            return Err(())

        val handler = def.unwrap()
        val ctx = BlockContext(
            span: block.payload_span,
            source: block.payload
        )

        match handler.parse_payload(block.payload, ctx):
            case Ok(value):
                Ok(ResolvedBlock(
                    kind: block.kind,
                    value: value,
                    span: block.span,
                    payload_span: block.payload_span
                ))
            case Err(err):
                self.diagnostics = self.diagnostics.push(
                    Diagnostic.error(err.message, err.span ?? block.payload_span)
                )
                Err(())
```

### Task 4.2: Integration Point

**Modify compiler pipeline:**

```simple
# In simple/compiler/driver.spl or equivalent

fn compile(source: text) -> Result<Module, [Diagnostic]>:
    # Phase 1: Lexer
    val lexer = Lexer.new(source)

    # Phase 2: TreeSitter (outline)
    val ts = TreeSitter.new(source)
    val outline = ts.parse_outline()

    # Phase 3: Block Resolution (NEW)
    val (resolved, block_errors) = BlockResolver.resolve_module(outline)
    if block_errors.len() > 0:
        return Err(block_errors)

    # Phase 4: Full Parser
    val parser = Parser.new(source, resolved)
    val ast = parser.parse()?

    # Phase 5: HIR, MIR, etc.
    ...
```

---

## Phase 5: Parser Integration

### Task 5.1: Update Expression Parsing

**File:** `simple/compiler/parser.spl`

```simple
struct Parser:
    ...
    resolved_blocks: Dict<Span, ResolvedBlock>  # Lookup by span

me parse_primary_expr() -> Expr:
    match self.peek():
        ...
        case BlockStart(kind):
            self.parse_resolved_block(kind)

        # Legacy support
        case KwLoss:
            self.parse_legacy_loss_block()
        case KwNograd:
            self.parse_legacy_nograd_block()
        ...

me parse_resolved_block(kind: text) -> Expr:
    val start = self.current.span
    self.advance()  # Consume BlockStart

    # Look up pre-resolved value
    val resolved = self.resolved_blocks.get(start)
    if resolved.?:
        val block = resolved.unwrap()
        # Skip payload tokens (already processed)
        self.skip_to_block_end()
        self.expect(TokenKind.BlockEnd, "Expected '}' after block")

        Expr(
            kind: ExprKind.Block(block.kind, block.value),
            span: start.merge(self.previous.span)
        )
    else:
        # Fallback for inline parsing
        self.parse_block_inline(kind, start)
```

### Task 5.2: Add Block Expression Kind

```simple
enum ExprKind:
    ...
    # Generic block (new)
    Block(kind: text, value: BlockValue)

    # Legacy (keep for compatibility)
    LossBlock(body: Block)
    NogradBlock(body: Block)
```

---

## Phase 6: HIR/MIR Integration

### Task 6.1: Block IR Node

**File:** `simple/compiler/hir.spl`

```simple
enum HIRExpr:
    ...
    Block(kind: text, value: BlockValue, result_type: Type)
```

### Task 6.2: Block Lowering

**File:** `simple/compiler/mir.spl`

```simple
fn lower_block(block: HIRExpr.Block) -> MIRExpr:
    val def = BlockRegistry.default().lookup(block.kind).unwrap()

    # Check for compile-time evaluation
    val const_val = def.eval_const(block.value)
    if const_val.?:
        return MIRExpr.Const(const_val.unwrap())

    # Runtime lowering
    def.lower(block.value, LoweringContext.current())
```

---

## Phase 7: Standard Block Implementations

### Task 7.1: Shell Block (`sh{}`)

```simple
struct ShellBlockDef: BlockDefinition:
    fn kind() -> text: "sh"

    fn lexer_mode() -> LexerMode:
        LexerMode.Raw

    fn parse_payload(payload: text, ctx: BlockContext) -> Result<BlockValue, BlockError>:
        # Parse shell syntax (basic validation)
        val commands = ShellParser.parse(payload)?
        Ok(BlockValue.Shell(commands))

    fn lower(value: BlockValue, ctx: LoweringContext) -> MIR:
        # Generate: std.shell.exec(commands)
        ctx.emit_call("std.shell.exec", [value.as_shell()])
```

### Task 7.2: SQL Block (`sql{}`)

```simple
struct SqlBlockDef: BlockDefinition:
    fn kind() -> text: "sql"

    fn lexer_mode() -> LexerMode:
        LexerMode.Raw

    fn parse_payload(payload: text, ctx: BlockContext) -> Result<BlockValue, BlockError>:
        val query = SqlParser.parse(payload)?
        Ok(BlockValue.Sql(query))

    fn lower(value: BlockValue, ctx: LoweringContext) -> MIR:
        ctx.emit_call("std.sql.prepare", [value.as_sql()])
```

### Task 7.3: Regex Block (`re{}`)

```simple
struct RegexBlockDef: BlockDefinition:
    fn kind() -> text: "re"

    fn lexer_mode() -> LexerMode:
        LexerMode.Raw

    fn parse_payload(payload: text, ctx: BlockContext) -> Result<BlockValue, BlockError>:
        # Validate regex at compile time
        val pattern = Regex.compile(payload)?
        Ok(BlockValue.Regex(pattern))

    fn eval_const(value: BlockValue) -> ConstValue?:
        # Regex can be compiled at compile time
        Some(ConstValue.Regex(value.as_regex()))
```

---

## Testing Strategy

### Unit Tests

```simple
# test/compiler/blocks/registry_spec.spl
describe "BlockRegistry":
    it "registers custom blocks":
        val reg = BlockRegistry()
        reg.register(TestBlockDef())
        assert reg.lookup("test").?

    it "returns None for unknown blocks":
        val reg = BlockRegistry()
        assert not reg.lookup("unknown").?

# test/compiler/blocks/lexer_spec.spl
describe "Block tokenization":
    it "detects registered block keywords":
        val lexer = Lexer.new("test{ payload }")
        lexer.block_registry.register(TestBlockDef())
        val token = lexer.next_token()
        assert token.kind == TokenKind.BlockStart("test")
```

### Integration Tests

```simple
# test/compiler/blocks/integration_spec.spl
describe "Custom blocks end-to-end":
    it "compiles math block":
        val result = compile("val x = m{ a^2 + b^2 }")
        assert result.is_ok()

    it "compiles shell block":
        val result = compile("val out = sh{ ls -la }")
        assert result.is_ok()

    it "reports errors with correct spans":
        val result = compile("val x = sql{ SELECT * FORM users }")
        assert result.is_err()
        assert result.err().span.contains("FORM")
```

---

## Timeline

| Week | Phase | Tasks | Deliverables |
|------|-------|-------|--------------|
| 1 | Infrastructure | 1.1, 1.2 | Block module, refactored built-ins |
| 2 | Lexer | 2.1, 2.2, 2.3, 2.4 | Generic block tokenization |
| 2 | TreeSitter | 3.1, 3.2 | BlockOutline capture |
| 3 | Resolution | 4.1, 4.2 | BlockResolver phase |
| 3 | Parser | 5.1, 5.2 | Generic block parsing |
| 4 | HIR/MIR | 6.1, 6.2 | Block lowering |
| 5+ | Standard Blocks | 7.1, 7.2, 7.3 | sh{}, sql{}, re{} |

---

## Success Criteria

1. **Backward Compatibility**: All existing `m{}`, `loss{}`, `nograd{}` code works unchanged
2. **Extensibility**: Users can register custom blocks via `BlockRegistry`
3. **Error Quality**: Block errors show correct source locations within payload
4. **Performance**: Block resolution adds < 5% overhead to compilation
5. **IDE Support**: Blocks can provide syntax highlighting and completions

---

## Risks & Mitigations

| Risk | Impact | Mitigation |
|------|--------|------------|
| Breaking existing code | High | Comprehensive test suite, gradual rollout |
| Performance regression | Medium | Profile block resolution phase |
| Complex error mapping | Medium | Use payload spans for accurate diagnostics |
| User block security | Low | Document sandboxing requirements |

---

## Dependencies

- Lexer infrastructure (completed)
- TreeSitter outline parser (completed)
- Parser expression handling (completed)
- HIR/MIR pipeline (completed)

---

## Next Steps

1. Review design with stakeholders
2. Create feature branch
3. Implement Phase 1 (infrastructure)
4. Write unit tests
5. Iterate on remaining phases
