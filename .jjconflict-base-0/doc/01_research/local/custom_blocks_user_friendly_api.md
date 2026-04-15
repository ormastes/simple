# Custom Blocks User-Friendly API - Research Document

**Date:** 2026-02-05
**Status:** Research & Design Proposal
**Goal:** Make custom block creation as simple as possible for library authors

---

## Executive Summary

The current `BlockDefinition` trait is powerful but complex (20+ methods). This research proposes a simplified API that lets users create custom blocks with minimal boilerplate while still providing full power when needed.

**Key Insight:** 80% of custom blocks need only 3 things:
1. A keyword (`"myblock"`)
2. A lexer mode (`Raw`, `Math`, or `Normal`)
3. A parser function (`fn(text) -> Result`)

---

## Current API Complexity

### What Users Must Implement Today

```simple
struct MyBlockDef: BlockDefinition:
    fn kind() -> text: "myblock"

    fn lexer_mode() -> LexerMode: LexerMode.Raw

    fn syntax_features() -> SyntaxFeatures:
        SyntaxFeatures(power_caret: false, transpose_quote: false, ...)

    fn parse_payload(payload: text, ctx: BlockContext) -> Result<BlockValue, BlockError>:
        # 50+ lines of parsing logic
        ...

    fn validate(value: BlockValue, ctx: BlockContext) -> [BlockError]:
        []  # Usually empty

    fn eval_const(value: BlockValue) -> ConstValue?:
        None  # Usually not needed

    # 15+ more optional methods...
```

**Problems:**
- Too much boilerplate for simple blocks
- Must understand `SyntaxFeatures` struct (10+ fields)
- Must know about `BlockContext`, `BlockError`, `BlockValue` enums
- No guidance on common patterns
- Hard to discover capabilities

---

## Proposed User-Friendly API

### Design Principles

1. **Progressive Disclosure** - Simple by default, powerful when needed
2. **Smart Defaults** - Reasonable defaults for common cases
3. **Builder Pattern** - Fluent, discoverable API
4. **Type Safety** - Leverage Simple's type system
5. **Documentation** - Inline examples in API

---

## Three-Tier API Design

### Tier 1: Minimal Block (80% of use cases)

**Goal:** Define a custom block in 3 lines

```simple
import compiler.blocks.easy

# Simplest possible block - raw text capture
val my_block = block("myblock", LexerMode.Raw, \payload:
    Ok(BlockValue.Raw(payload))
)

register_block(my_block)
```

**Use case:** Simple text blocks (like heredocs, comments, embedded languages)

---

### Tier 2: Builder API (15% of use cases)

**Goal:** Declarative configuration with smart defaults

```simple
import compiler.blocks.builder

# Math-like block with custom operators
val matrix_block = BlockBuilder("matrix")
    .lexer_mode(LexerMode.Math)
    .enable_feature("matrix_mul")      # @ operator
    .enable_feature("transpose_quote")  # ' operator
    .parser(\payload, ctx:
        parse_matrix_syntax(payload)
    )
    .validator(\value, ctx:
        validate_dimensions(value)
    )
    .build()

register_block(matrix_block)
```

**Use case:** DSL blocks with special syntax (math, diagrams, queries)

---

### Tier 3: Full Trait (5% of use cases)

**Goal:** Complete control for advanced features

```simple
import compiler.blocks.definition

# Full control with all hooks
struct AdvancedBlock: BlockDefinition:
    fn kind() -> text: "advanced"

    # Implement all 20+ methods for full control
    fn lex(payload, pre_lex, ctx) -> [BlockToken]: ...
    fn treesitter_outline(payload, pre_lex) -> BlockOutlineInfo: ...
    fn parse_full(payload, pre_lex, ctx) -> BlockValue: ...
    fn highlight(payload) -> [HighlightToken]: ...
    fn completions(payload, cursor) -> [Completion]: ...
    # ... all other methods
```

**Use case:** Complex blocks with custom lexing, IDE support, compile-time evaluation

---

## Detailed API Specification

### Module: `compiler.blocks.easy`

**Purpose:** One-function block definition for simple cases

```simple
# Quick block registration (returns BlockDefinition)
fn block(
    kind: text,
    mode: LexerMode = LexerMode.Raw,
    parser: fn(text) -> Result<BlockValue, text>
) -> BlockDefinition

# With validation
fn block_with_validation(
    kind: text,
    mode: LexerMode,
    parser: fn(text) -> Result<BlockValue, text>,
    validator: fn(BlockValue) -> [text]
) -> BlockDefinition

# With compile-time evaluation
fn const_block(
    kind: text,
    mode: LexerMode,
    parser: fn(text) -> Result<BlockValue, text>,
    eval: fn(BlockValue) -> ConstValue?
) -> BlockDefinition
```

**Examples:**

```simple
# 1. Simple heredoc block
val heredoc = block("heredoc", LexerMode.Raw, \text:
    Ok(BlockValue.Raw(text.trim()))
)

# 2. Comment block (like Rust's /*! ... */)
val doc_comment = block("doc", LexerMode.Raw, \text:
    val lines = text.split("\n").map(\l: l.trim())
    Ok(BlockValue.Custom("DocComment", lines))
)

# 3. Color literal block
val color = const_block("color", LexerMode.Raw,
    \text:
        val hex = text.trim()
        if hex.starts_with("#") and hex.len() == 7:
            Ok(BlockValue.Custom("Color", hex))
        else:
            Err("Expected #RRGGBB color format")
    ,
    \value:
        match value:
            case Custom("Color", hex):
                Some(ConstValue.String(hex))
            case _:
                None
)

# Usage: val bg = color{ #FF5733 }
```

---

### Module: `compiler.blocks.builder`

**Purpose:** Fluent builder for declarative block configuration

```simple
struct BlockBuilder:
    """
    Fluent builder for custom blocks with smart defaults.

    Example:
        val sql = BlockBuilder("sql")
            .lexer_mode(LexerMode.Raw)
            .parser(\payload: parse_sql(payload))
            .enable_feature("named_params")
            .validator(\val: validate_sql_syntax(val))
            .build()
    """

    # Constructor
    static fn new(kind: text) -> BlockBuilder

    # Lexer configuration
    me lexer_mode(mode: LexerMode) -> BlockBuilder
    me raw_text() -> BlockBuilder                     # Shortcut for LexerMode.Raw
    me math_mode() -> BlockBuilder                    # Shortcut for LexerMode.Math
    me normal_mode() -> BlockBuilder                  # Shortcut for LexerMode.Normal

    # Syntax features (fluent enable/disable)
    me enable_feature(name: text) -> BlockBuilder     # "power_caret", "broadcast_ops", etc.
    me disable_feature(name: text) -> BlockBuilder
    me enable_all_math() -> BlockBuilder              # All math features
    me enable_pipelines() -> BlockBuilder             # |>, >>, <<

    # Core parsing
    me parser(fn: fn(text, BlockContext) -> Result<BlockValue, BlockError>) -> BlockBuilder
    me simple_parser(fn: fn(text) -> Result<BlockValue, text>) -> BlockBuilder  # Simpler signature

    # Validation (optional)
    me validator(fn: fn(BlockValue, BlockContext) -> [BlockError]) -> BlockBuilder
    me simple_validator(fn: fn(BlockValue) -> [text]) -> BlockBuilder

    # Compile-time evaluation (optional)
    me const_eval(fn: fn(BlockValue) -> ConstValue?) -> BlockBuilder

    # IDE support (optional)
    me highlighter(fn: fn(text) -> [HighlightToken]) -> BlockBuilder
    me completer(fn: fn(text, i64) -> [Completion]) -> BlockBuilder
    me hover_provider(fn: fn(text, i64) -> HoverInfo?) -> BlockBuilder

    # Build final block definition
    fn build() -> BlockDefinition
```

**Smart Defaults:**
- `lexer_mode`: `LexerMode.Raw` (safest default)
- `syntax_features`: All disabled (opt-in only)
- `validator`: Always succeeds
- `eval_const`: Returns `None` (no compile-time eval)
- IDE methods: Use basic default implementations

**Example 1: Shell Block (Simplified)**

```simple
val shell = BlockBuilder("sh")
    .raw_text()
    .simple_parser(\cmd:
        val commands = parse_shell_commands(cmd)
        if commands.?:
            Ok(BlockValue.Shell(commands))
        else:
            Err("Invalid shell syntax")
    )
    .simple_validator(\val:
        match val:
            case Shell(cmds):
                validate_portable_shell(cmds)  # Returns [text] errors
            case _:
                ["Expected shell commands"]
    )
    .build()
```

**Example 2: Diagram Block**

```simple
val diagram = BlockBuilder("diagram")
    .raw_text()
    .simple_parser(\text:
        match detect_diagram_format(text):
            case "mermaid":
                Ok(BlockValue.Custom("Diagram", parse_mermaid(text)))
            case "dot":
                Ok(BlockValue.Custom("Diagram", parse_dot(text)))
            case unknown:
                Err("Unknown diagram format: {unknown}")
    )
    .const_eval(\val:
        match val:
            case Custom("Diagram", data):
                Some(ConstValue.String(data.render_svg()))
            case _:
                None
    )
    .highlighter(\text:
        # Syntax highlighting for diagrams
        highlight_diagram_keywords(text)
    )
    .build()
```

**Example 3: Custom Math Block**

```simple
val tensor = BlockBuilder("tensor")
    .math_mode()
    .enable_feature("broadcast_ops")     # .+ .- .* ./
    .enable_feature("matrix_mul")        # @
    .enable_feature("power_caret")       # ^
    .simple_parser(\expr:
        parse_tensor_expr(expr)
    )
    .simple_validator(\val:
        check_tensor_dimensions(val)
    )
    .build()
```

---

### Module: `compiler.blocks.utils`

**Purpose:** Utility functions for common block operations

```simple
# Pre-built parsers
fn parse_json(text: text) -> Result<BlockValue, text>
fn parse_yaml(text: text) -> Result<BlockValue, text>
fn parse_toml(text: text) -> Result<BlockValue, text>
fn parse_xml(text: text) -> Result<BlockValue, text>
fn parse_csv(text: text) -> Result<BlockValue, text>

# Pre-built validators
fn validate_json(value: BlockValue) -> [text]
fn validate_regex(value: BlockValue) -> [text]
fn validate_sql(value: BlockValue, dialect: text = "ansi") -> [text]

# Syntax highlighting helpers
fn highlight_keywords(text: text, keywords: [text]) -> [HighlightToken]
fn highlight_strings(text: text) -> [HighlightToken]
fn highlight_comments(text: text, line_comment: text, block_comment: (text, text)?) -> [HighlightToken]
fn highlight_numbers(text: text) -> [HighlightToken]

# Error message helpers
fn error_at(ctx: BlockContext, message: text, offset: i64, length: i64 = 1) -> BlockError
fn error_span(ctx: BlockContext, message: text, span: (i64, i64)) -> BlockError
fn errors_from_strings(ctx: BlockContext, messages: [text]) -> [BlockError]

# Common patterns
fn interpolate_variables(text: text, vars: Dict<text, text>) -> text
fn strip_indent(text: text) -> text
fn normalize_newlines(text: text) -> text
```

**Example: YAML Block in 5 Lines**

```simple
import compiler.blocks.easy
import compiler.blocks.utils

val yaml = block("yaml", LexerMode.Raw, \text:
    parse_yaml(text)
)
```

---

## Feature Enablement Reference

### Available Feature Names

**Math Operators:**
- `"power_caret"` - Enable `^` for exponentiation (e.g., `x^2`)
- `"transpose_quote"` - Enable `'` for matrix transpose (e.g., `A'`)
- `"implicit_multiplication"` - Enable `2x` and `(a)(b)` syntax
- `"broadcast_ops"` - Enable `.+`, `.-`, `.*`, `./`, `.^`
- `"matrix_mul"` - Enable `@` for matrix multiplication

**Pipeline Operators:**
- `"pipe_forward"` - Enable `|>` operator
- `"pipe_backward"` - Enable `<|` operator
- `"compose_forward"` - Enable `>>` operator
- `"compose_backward"` - Enable `<<` operator
- `"parallel"` - Enable `//` operator

**Deep Learning:**
- `"auto_backward"` - Automatically call `.backward()` on result
- `"disable_grad"` - Disable gradient tracking in block
- `"layer_connect"` - Enable `~>` for layer composition

**Custom:**
- `"custom_keywords: [word1, word2]"` - Add custom keywords

**Presets:**
```simple
.enable_all_math()       # All math features
.enable_pipelines()      # All pipeline operators
.enable_deep_learning()  # auto_backward + layer_connect
```

---

## Registration API

### Global Registry Functions

```simple
# Register a block definition
fn register_block(def: BlockDefinition)

# Unregister a block
fn unregister_block(kind: text) -> bool

# Check if block is registered
fn is_block_registered(kind: text) -> bool

# Get registered block
fn get_block(kind: text) -> BlockDefinition?

# List all registered blocks
fn list_blocks() -> [text]

# Scoped registration (for testing)
fn with_block<T>(def: BlockDefinition, body: fn() -> T) -> T
```

**Example: Temporary Block Registration**

```simple
# Register block for test scope only
with_block(my_test_block, \:
    val result = myblock{ test content }
    assert(result == expected)
)
# Block automatically unregistered after scope
```

---

## Error Handling Best Practices

### Error Types

```simple
# Simple string error (auto-converted)
Err("Invalid syntax")

# Structured error with span
Err(error_at(ctx, "Expected closing brace", offset: 42))

# Multiple errors
val errors = [
    error_at(ctx, "Missing semicolon", 10),
    error_at(ctx, "Unknown identifier", 20)
]
```

### Error Message Guidelines

1. **Be specific:** `"Expected closing brace at line 5"` not `"Syntax error"`
2. **Show location:** Include line/column when possible
3. **Suggest fixes:** `"Did you mean 'SELECT'?"`
4. **Be consistent:** Follow Simple's error message style

---

## Testing Custom Blocks

### Test Utilities

```simple
# Test helper module
import compiler.blocks.testing

# Parse and assert
fn test_parse(block_kind: text, payload: text, expected: BlockValue)

# Parse and assert error
fn test_parse_error(block_kind: text, payload: text, expected_message: text)

# Test validation
fn test_validate(block_kind: text, value: BlockValue, expected_errors: [text])

# Test compile-time evaluation
fn test_const_eval(block_kind: text, value: BlockValue, expected: ConstValue)
```

---

## Common Patterns & Recipes

### Pattern 1: Simple Text Block

```simple
# Raw text with trimming
val heredoc = block("heredoc", LexerMode.Raw, \text:
    Ok(BlockValue.Raw(text.trim()))
)
```

### Pattern 2: DSL with Validation

```simple
# SQL with dialect validation
val sql = BlockBuilder("sql")
    .raw_text()
    .parser(\payload, ctx:
        parse_sql(payload, dialect: "postgres")
    )
    .validator(\value, ctx:
        validate_sql_dialect(value, "postgres")
    )
    .build()
```

### Pattern 3: Math-Like Syntax

```simple
# Custom tensor notation
val tensor = BlockBuilder("tensor")
    .math_mode()
    .enable_all_math()
    .parser(\expr, ctx:
        parse_tensor_notation(expr)
    )
    .build()
```

### Pattern 4: Compile-Time Constant

```simple
# Regex compiled at compile-time
val re = const_block("re", LexerMode.Raw,
    \pattern: compile_regex(pattern),
    \value: extract_regex_pattern(value)
)
```

### Pattern 5: IDE-Friendly Block

```simple
# Block with full IDE support
val graphql = BlockBuilder("graphql")
    .raw_text()
    .parser(\query: parse_graphql(query))
    .highlighter(\text: highlight_graphql(text))
    .completer(\text, pos: complete_graphql(text, pos))
    .hover_provider(\text, pos: hover_graphql(text, pos))
    .build()
```

---

## Migration Guide

### From Current API to New API

**Before (Complex):**
```simple
struct MyBlockDef: BlockDefinition:
    fn kind() -> text: "myblock"
    fn lexer_mode() -> LexerMode: LexerMode.Raw
    fn syntax_features() -> SyntaxFeatures:
        SyntaxFeatures(power_caret: false, ...)
    fn parse_payload(...): ...
    fn validate(...): []
    fn eval_const(...): None
    # ... 15 more methods

register_block(MyBlockDef())
```

**After (Simple):**
```simple
val myblock = BlockBuilder("myblock")
    .raw_text()
    .simple_parser(\text: parse_my_block(text))
    .build()

register_block(myblock)
```

**After (Minimal):**
```simple
register_block(block("myblock", LexerMode.Raw, parse_my_block))
```

---

## Performance Considerations

### Smart Defaults are Fast

- `LexerMode.Raw` - Zero overhead (captures as string)
- `BlockBuilder` - Compiled away at build time
- `simple_parser` - Unwraps to full parser signature
- Default validators - Empty array (no validation)

### When to Use Full Trait

Use full `BlockDefinition` trait only when you need:
1. **Custom lexing** - Special tokenization rules
2. **TreeSitter outline** - Fast structural extraction
3. **Incremental parsing** - IDE performance optimization
4. **Advanced IDE features** - Custom signature help, refactorings

For 95% of blocks, the builder API is sufficient and faster to write.

---

## Documentation Requirements

All registered blocks should provide:

1. **Docstring** - What the block does
2. **Syntax examples** - How to use it
3. **Error examples** - Common mistakes
4. **Type signature** - What it returns

**Example:**

```simple
val sql = BlockBuilder("sql")
    .doc("""
        SQL query block with dialect support.

        Example:
            val users = sql{ SELECT * FROM users WHERE age > 21 }

        Returns: BlockValue.Sql(query: SqlQuery)

        Errors:
            - "Unknown table: foo" - Table not found
            - "Syntax error near 'SELCT'" - Typo in keyword
    """)
    .raw_text()
    .parser(\payload: parse_sql(payload))
    .build()
```

---

## Future Enhancements

### Phase 2: Package Manager Integration

```simple
# Install blocks from registry
simple install blocks/yaml
simple install blocks/graphql
simple install blocks/protobuf

# blocks/yaml/block.spl
export val yaml_block = BlockBuilder("yaml")...
```

### Phase 3: Block Composition

```simple
# Compose existing blocks
val template = BlockBuilder("template")
    .compose_with(sql_block)      # Embed SQL in templates
    .compose_with(markdown_block) # Embed markdown
    .parser(\payload: parse_template(payload))
    .build()
```

### Phase 4: Macro Blocks

```simple
# Blocks that generate code
val component = macro_block("component", \payload:
    generate_react_component(payload)
)
```

---

## Summary

### Key Improvements

1. **Reduced boilerplate:** 3 lines vs 50+ lines for simple blocks
2. **Progressive disclosure:** Simple → Builder → Full trait
3. **Smart defaults:** Sensible choices for common cases
4. **Discoverable API:** Fluent builder with method chaining
5. **Type safety:** Compile-time validation of features
6. **Testing utilities:** Easy to test custom blocks
7. **Documentation:** Inline examples and guidelines

### User Journey

1. **Beginner:** Use `block()` for simple text blocks
2. **Intermediate:** Use `BlockBuilder` for DSLs
3. **Advanced:** Implement full `BlockDefinition` trait for complex features

### Next Steps

1. Implement `compiler.blocks.easy` module
2. Implement `compiler.blocks.builder` module
3. Implement `compiler.blocks.utils` module
4. Write SSpec tests for all APIs
5. Migrate built-in blocks to new API as examples
6. Update documentation and tutorials
