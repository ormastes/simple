# Custom Blocks Quick Reference

**Last Updated:** 2026-02-05
**Target Audience:** Simple library authors creating custom blocks

---

## 30-Second Quick Start

```simple
import compiler.blocks.easy

# Define your block
val my_block = block("myblock", LexerMode.Raw, \payload:
    Ok(BlockValue.Raw(payload))
)

# Register it
register_block(my_block)

# Use it
val result = myblock{ content here }
```

---

## Choosing the Right API

| Use Case | API | Example |
|----------|-----|---------|
| Simple text block | `block()` | Heredocs, comments |
| DSL with features | `BlockBuilder` | SQL, GraphQL, diagrams |
| Full control | `BlockDefinition` trait | Complex IDE integration |

**Rule of Thumb:** Start with `block()`, upgrade to `BlockBuilder` if you need features, implement full trait only for advanced IDE support.

---

## API Signatures

### Tier 1: Minimal API

```simple
# Basic block
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

### Tier 2: Builder API

```simple
struct BlockBuilder:
    # Constructor
    static fn new(kind: text) -> BlockBuilder

    # Lexer modes (shortcuts)
    me raw_text() -> BlockBuilder
    me math_mode() -> BlockBuilder
    me normal_mode() -> BlockBuilder

    # Features (fluent)
    me enable_feature(name: text) -> BlockBuilder
    me enable_all_math() -> BlockBuilder
    me enable_pipelines() -> BlockBuilder

    # Parsing
    me simple_parser(fn: fn(text) -> Result<BlockValue, text>) -> BlockBuilder
    me parser(fn: fn(text, BlockContext) -> Result<BlockValue, BlockError>) -> BlockBuilder

    # Validation
    me simple_validator(fn: fn(BlockValue) -> [text]) -> BlockBuilder

    # Compile-time eval
    me const_eval(fn: fn(BlockValue) -> ConstValue?) -> BlockBuilder

    # IDE support
    me highlighter(fn: fn(text) -> [HighlightToken]) -> BlockBuilder
    me completer(fn: fn(text, i64) -> [Completion]) -> BlockBuilder

    # Build
    fn build() -> BlockDefinition
```

---

## Lexer Modes

| Mode | When to Use | Example |
|------|-------------|---------|
| `LexerMode.Raw` | Text blocks, no special syntax | Heredocs, JSON, SQL |
| `LexerMode.Math` | Math/scientific notation | Tensors, equations |
| `LexerMode.Normal` | Standard Simple syntax | Templates with interpolation |

**Default:** `LexerMode.Raw` (safest choice)

---

## Syntax Features

### Available Features

**Math Operators:**
- `"power_caret"` - `x^2` (caret as power)
- `"transpose_quote"` - `A'` (quote as transpose)
- `"implicit_multiplication"` - `2x`, `(a)(b)`
- `"broadcast_ops"` - `.+`, `.-`, `.*`, `./`, `.^`
- `"matrix_mul"` - `@` operator

**Pipeline Operators:**
- `"pipe_forward"` - `|>` operator
- `"compose_forward"` - `>>` operator
- `"compose_backward"` - `<<` operator

**Deep Learning:**
- `"auto_backward"` - Auto `.backward()` call
- `"disable_grad"` - Disable gradient tracking
- `"layer_connect"` - `~>` for layer composition

### Presets

```simple
.enable_all_math()       # All math features
.enable_pipelines()      # All pipeline operators
.enable_deep_learning()  # DL features
```

---

## Common Patterns

### Pattern 1: Simple Text Block

```simple
val heredoc = block("heredoc", LexerMode.Raw, \text:
    Ok(BlockValue.Raw(text.trim()))
)
```

### Pattern 2: JSON/Data Format

```simple
val json = BlockBuilder("json")
    .raw_text()
    .simple_parser(\text: parse_json(text))
    .build()
```

### Pattern 3: Math DSL

```simple
val tensor = BlockBuilder("tensor")
    .math_mode()
    .enable_all_math()
    .simple_parser(\expr: parse_tensor(expr))
    .build()
```

### Pattern 4: With Validation

```simple
val sql = BlockBuilder("sql")
    .raw_text()
    .simple_parser(\text: parse_sql(text))
    .simple_validator(\val: validate_sql(val))
    .build()
```

### Pattern 5: Compile-Time Constant

```simple
val re = const_block("re", LexerMode.Raw,
    \pattern: compile_regex(pattern),
    \value: extract_pattern(value)
)
```

### Pattern 6: With IDE Support

```simple
val graphql = BlockBuilder("graphql")
    .raw_text()
    .simple_parser(\text: parse_graphql(text))
    .highlighter(\text: highlight_graphql(text))
    .completer(\text, pos: complete_graphql(text, pos))
    .build()
```

---

## BlockValue Types

```simple
enum BlockValue:
    Raw(text: text)                    # Plain text
    Expr(expr: Any)                    # Expression
    Shell(commands: ShellCommands)     # Shell commands
    Sql(query: SqlQuery)               # SQL query
    Regex(pattern: RegexPattern)       # Regex pattern
    Json(value: JsonValue)             # JSON data
    Markdown(doc: MarkdownDoc)         # Markdown
    Custom(type_name: text, data: Any) # Custom type
```

**Return types:**
- Use `Raw(text)` for simple text blocks
- Use `Custom(name, data)` for custom types
- Use built-in types for standard formats

---

## Error Handling

### Simple Errors (String)

```simple
\text:
    if invalid:
        Err("Invalid syntax")
    else:
        Ok(BlockValue.Raw(text))
```

### Structured Errors

```simple
import compiler.blocks.utils

\text, ctx:
    if invalid:
        Err(error_at(ctx, "Invalid syntax", offset: 10))
    else:
        Ok(BlockValue.Raw(text))
```

### Multiple Errors

```simple
\value:
    val errors = []
    if not value.is_valid():
        errors.push("Invalid structure")
    if not value.is_complete():
        errors.push("Incomplete data")
    errors  # Return [text]
```

---

## Registration

```simple
# Register globally
register_block(my_block)

# Unregister
unregister_block("myblock")

# Check if registered
is_block_registered("myblock")

# Get block definition
get_block("myblock")

# List all blocks
list_blocks()

# Scoped registration (for tests)
with_block(my_block, \:
    # Block available here
    val result = myblock{ content }
    result
)
# Auto-unregistered after scope
```

---

## Utility Functions

### Pre-built Parsers

```simple
import compiler.blocks.utils

parse_json(text: text) -> Result<BlockValue, text>
parse_yaml(text: text) -> Result<BlockValue, text>
parse_toml(text: text) -> Result<BlockValue, text>
parse_xml(text: text) -> Result<BlockValue, text>
parse_csv(text: text) -> Result<BlockValue, text>
```

### Pre-built Validators

```simple
validate_json(value: BlockValue) -> [text]
validate_regex(value: BlockValue) -> [text]
validate_sql(value: BlockValue, dialect: text = "ansi") -> [text]
```

### Syntax Highlighting

```simple
highlight_keywords(text: text, keywords: [text]) -> [HighlightToken]
highlight_strings(text: text) -> [HighlightToken]
highlight_comments(text: text, line_comment: text, block_comment: (text, text)?) -> [HighlightToken]
highlight_numbers(text: text) -> [HighlightToken]
```

### Error Helpers

```simple
error_at(ctx: BlockContext, message: text, offset: i64, length: i64 = 1) -> BlockError
error_span(ctx: BlockContext, message: text, span: (i64, i64)) -> BlockError
errors_from_strings(ctx: BlockContext, messages: [text]) -> [BlockError]
```

### Common Utilities

```simple
interpolate_variables(text: text, vars: Dict<text, text>) -> text
strip_indent(text: text) -> text
normalize_newlines(text: text) -> text
```

---

## Complete Examples

### Example 1: Heredoc (3 lines)

```simple
register_block(block("heredoc", LexerMode.Raw, \text:
    Ok(BlockValue.Raw(text.trim()))
))

val doc = heredoc{
    Multi-line
    text content
}
```

### Example 2: JSON (5 lines)

```simple
register_block(BlockBuilder("json")
    .raw_text()
    .simple_parser(\text: parse_json(text))
    .build()
)

val data = json{ {"name": "Alice"} }
```

### Example 3: SQL with Validation (8 lines)

```simple
register_block(BlockBuilder("sql")
    .raw_text()
    .simple_parser(\text: parse_sql(text))
    .simple_validator(\val: validate_sql(val, "postgres"))
    .build()
)

val users = sql{
    SELECT name, age FROM users WHERE age > 21
}
```

### Example 4: Tensor Math (10 lines)

```simple
register_block(BlockBuilder("tensor")
    .math_mode()
    .enable_all_math()
    .simple_parser(\expr: parse_tensor(expr))
    .simple_validator(\val: check_dimensions(val))
    .build()
)

val result = tensor{
    A @ B^2 + C' .* D
}
```

### Example 5: GraphQL with IDE (15 lines)

```simple
register_block(BlockBuilder("graphql")
    .raw_text()
    .simple_parser(\text: parse_graphql(text))
    .highlighter(\text: highlight_graphql(text))
    .completer(\text, pos: complete_graphql(text, pos))
    .hover_provider(\text, pos: hover_graphql(text, pos))
    .build()
)

val query = graphql{
    query GetUser($id: ID!) {
        user(id: $id) {
            name
            email
        }
    }
}
```

---

## Testing

```simple
import compiler.blocks.testing

test_parse("myblock", "payload", expected: BlockValue.Raw("payload"))
test_parse_error("myblock", "bad", expected_message: "Invalid syntax")
test_validate("myblock", value, expected_errors: ["Error 1"])
test_const_eval("myblock", value, expected: ConstValue.String("result"))
```

---

## Performance Tips

1. **Use `LexerMode.Raw`** for best performance (no tokenization)
2. **Enable only needed features** - each feature adds overhead
3. **Simple parsers are fast** - avoid complex parsing logic
4. **Validation is optional** - skip if not needed
5. **Compile-time eval is free** - happens at build time

---

## Best Practices

### ✅ DO

- Start simple, add features as needed
- Use descriptive block names (`sql`, `json`, not `block1`)
- Return specific `BlockValue` types when possible
- Provide helpful error messages with locations
- Write tests for your blocks
- Document syntax and examples
- Use utility functions for common patterns

### ❌ DON'T

- Don't enable features you don't need
- Don't parse at registration time (lazy parse)
- Don't return `BlockValue.Error` in parser (use `Err()`)
- Don't forget to unregister in tests
- Don't skip validation for user-facing blocks
- Don't implement full trait unless absolutely needed

---

## Troubleshooting

### "Unknown block keyword: myblock"

→ Did you call `register_block(my_block)`?

### "Expected text, got BlockValue"

→ Check your parser returns `Result<BlockValue, text>`

### "Lexer error: unexpected token"

→ Wrong `LexerMode`? Try `LexerMode.Raw` for plain text

### "Feature not enabled: power_caret"

→ Add `.enable_feature("power_caret")` to your builder

### "IDE features not working"

→ Implement `.highlighter()`, `.completer()`, `.hover_provider()`

---

## Migration from Full Trait

**Before (50+ lines):**
```simple
struct MyBlock: BlockDefinition:
    fn kind() -> text: "myblock"
    fn lexer_mode() -> LexerMode: LexerMode.Raw
    fn syntax_features() -> SyntaxFeatures: SyntaxFeatures(...)
    fn parse_payload(...): ...
    # ... 15 more methods
```

**After (5 lines):**
```simple
val my_block = BlockBuilder("myblock")
    .raw_text()
    .simple_parser(\text: parse_my_block(text))
    .build()
```

---

## Further Reading

- **Full Documentation:** `doc/research/custom_blocks_user_friendly_api.md`
- **SSpec Tests:** `test/compiler/custom_blocks_easy_api_spec.spl`
- **Built-in Examples:** `src/compiler/blocks/builtin_blocks_defs.spl`
- **Design Proposals:** `doc/design/custom_blocks_proposal.md`

---

## Quick Decision Tree

```
Need custom block?
 │
 ├─ Just text/data? → Use block()
 │
 ├─ DSL with operators? → Use BlockBuilder + enable_feature()
 │
 ├─ Math/science syntax? → Use .math_mode() + enable_all_math()
 │
 ├─ Need IDE support? → Use .highlighter() + .completer()
 │
 └─ Complex lexing/parsing? → Implement BlockDefinition trait
```

---

**Questions?** See `/doc/guide/custom_blocks_tutorial.md` or ask in community forums.
