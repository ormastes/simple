# Unified Parser Architecture - Design Document

**Date:** 2026-02-04
**Status:** Design Proposal
**Related:** `doc/research/parser_duplication_analysis_2026-02-04.md`

## Overview

This document defines the unified architecture for Simple language parsing after merging duplicate implementations.

**Goals:**
1. Single source of truth for Simple language lexer, parser, treesitter
2. Clear separation between core language parsing and specialized parsers
3. Reusable components for compiler, interpreter, LSP, and tools
4. Maintainable, well-documented architecture

---

## Architecture Principles

### 1. Single Canonical Implementation

**Core Language Components (Simple syntax):**
- ✅ ONE lexer: `src/compiler/lexer.spl`
- ✅ ONE parser: `src/compiler/parser.spl`
- ✅ ONE outline parser: `src/compiler/treesitter.spl`

**Specialized Components (Other languages/formats):**
- Separate parsers for SDN, IR DSL, predicates, etc.
- Clearly documented as domain-specific, not duplicates

### 2. Layered Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│ High-Level APIs                                                  │
│ - Compiler Driver (src/compiler/driver.spl)                     │
│ - Interpreter Wrapper (src/app/interpreter/parser.spl)          │
│ - LSP Server (future)                                           │
└─────────────────────────────────────────────────────────────────┘
                              ↓ uses
┌─────────────────────────────────────────────────────────────────┐
│ Core Parsing Components                                          │
│ - Parser (src/compiler/parser.spl)          - Full AST parsing  │
│ - TreeSitter (src/compiler/treesitter.spl)  - Outline parsing   │
│ - Lexer (src/compiler/lexer.spl)            - Tokenization      │
└─────────────────────────────────────────────────────────────────┘
                              ↓ uses
┌─────────────────────────────────────────────────────────────────┐
│ Type Definitions                                                 │
│ - parser_types.spl   - AST types (Module, Function, Class, ...) │
│ - treesitter_types.spl - Outline types (OutlineModule, ...)     │
│ - lexer_types.spl    - Token types (Token, TokenKind, Span)     │
└─────────────────────────────────────────────────────────────────┘
```

### 3. Reusability Contract

**All consumers of parsing use the same core components:**

| Consumer | Uses | Purpose |
|----------|------|---------|
| Compiler | Parser → TreeSitter → Lexer | Full compilation |
| Interpreter | TreeSitter (wrapper) | Fast outline + execution |
| LSP Server | TreeSitter (IDE mode) | Quick navigation, errors |
| Test Runner | TreeSitter | Extract test declarations |
| Doc Generator | TreeSitter | Generate API docs |

---

## Component Specifications

### Lexer (`src/compiler/lexer.spl`)

**Responsibility:** Convert source text into token stream

**Features:**
- Full Unicode support
- String interpolation
- Indentation tracking (INDENT/DEDENT tokens)
- Math block mode (enables `^` operator)
- Block system integration
- Generic depth tracking (for `>>` disambiguation)
- Implicit multiplication detection
- Error recovery

**API:**
```simple
struct Lexer:
    source: text
    pos, line, col: i64
    indent_stack: [i64]
    in_math_block: bool
    block_registry: BlockRegistry?
    # ... (internal state)

impl Lexer:
    static fn new(source: text) -> Lexer
    static fn with_registry(source, registry) -> Lexer
    me next_token() -> Token
    me peek_token() -> Token
    me tokenize() -> [Token]
    # ... (internal methods)
```

**Token Output:**
```simple
struct Token:
    kind: TokenKind
    span: Span
    lexeme: text

enum TokenKind:
    # Literals
    Integer(i64), Float(f64), String(text), Bool(bool), Nil
    # Identifiers
    Identifier(text)
    # Keywords
    Val, Var, Fn, Class, Struct, Enum, Trait, Impl, ...
    # Operators
    Plus, Minus, Star, Slash, Power, Caret, ...
    # Delimiters
    LParen, RParen, LBrace, RBrace, LBracket, RBracket
    # Special
    Newline, Indent, Dedent, Eof, Error(text)
```

**Modes:**
- `Normal` - Standard Simple syntax
- `Math` - Math block (enables `^` as power)
- `Raw` - Raw block (sh{}, sql{} - no interpolation)
- `Custom` - Block-defined custom lexing

---

### TreeSitter (`src/compiler/treesitter.spl`)

**Responsibility:** Fast outline parsing (structure without full bodies)

**Features:**
- Two-pass parsing support (outline → full bodies)
- Extracts: imports, exports, functions, classes, structs, enums, traits, impls
- Doc comment accumulation
- Block outline extraction
- Fast mode (skip Skippable blocks)
- Error collection

**API:**
```simple
struct TreeSitter:
    lexer: Lexer
    current, previous: Token
    errors: [ParseError]
    doc_comment: text?
    inline_blocks: [BlockOutline]
    fast_mode: bool
    registry: BlockRegistry?

impl TreeSitter:
    static fn new(source: text) -> TreeSitter
    static fn with_fast_mode(fast_mode: bool) -> TreeSitter
    me with_source(source: text) -> TreeSitter
    me parse_outline() -> OutlineModule
    # ... (internal parsing methods)
```

**Outline Output:**
```simple
struct OutlineModule:
    name: text
    imports: [ImportOutline]
    exports: [ExportOutline]
    functions: [FunctionOutline]
    classes: [ClassOutline]
    structs: [StructOutline]
    enums: [EnumOutline]
    traits: [TraitOutline]
    impls: [ImplOutline]
    type_aliases: [TypeAliasOutline]
    constants: [ConstantOutline]
    inline_blocks: [BlockOutline]
    errors: [ParseError]

struct FunctionOutline:
    name: text
    visibility: Visibility
    params: [ParamOutline]  # Just types, no bodies
    return_type: TypeExpr?
    type_params: [text]
    span: Span
    doc: text?
    # NOTE: body is NOT included (will be parsed later)
```

**Use Cases:**
1. **Compiler**: Get outline, then parse full bodies
2. **LSP**: Quick navigation, symbol list
3. **Test Runner**: Extract test function names
4. **Doc Generator**: API documentation

---

### Parser (`src/compiler/parser.spl`)

**Responsibility:** Full AST parsing (complete module with all bodies)

**Features:**
- Two-pass: Uses TreeSitter outline, then fills bodies
- Complete expression parsing
- Statement parsing
- Type expression parsing
- Pattern matching parsing
- Block expression parsing

**API:**
```simple
struct Parser:
    source: text
    lexer: Lexer
    current, previous: Token
    errors: [ParseError]
    outline: OutlineModule?
    resolved_blocks: ResolvedModule?

impl Parser:
    static fn new(source: text) -> Parser
    static fn with_resolved_blocks(source, resolved) -> Parser
    me parse() -> Module
    me parse_full() -> Module
    me parse_function_body(outline: FunctionOutline) -> Function
    me parse_class_body(outline: ClassOutline) -> Class
    # ... (internal parsing methods)
```

**Full AST Output:**
```simple
struct Module:
    name: text
    imports: [Import]
    exports: [Export]
    functions: Dict<text, Function>
    classes: Dict<text, Class>
    structs: Dict<text, Struct>
    enums: Dict<text, Enum>
    traits: Dict<text, Trait>
    impls: [Impl]
    type_aliases: Dict<text, TypeAlias>
    constants: Dict<text, Constant>

struct Function:
    name: text
    visibility: Visibility
    params: [Param]
    return_type: TypeExpr?
    type_params: [text]
    body: Expr              # ← Full body expression
    span: Span
    doc: text?
```

**Parsing Strategy:**
```simple
# Step 1: Get outline (fast, no bodies)
val ts = TreeSitter.new(source)
val outline = ts.parse_outline()

# Step 2: Parse full module with bodies
val parser = Parser.with_resolved_blocks(source, outline)
val module = parser.parse_full()
```

---

## Specialized Parsers (Not Duplicates)

### SDN Parser (`src/lib/sdn/parser.spl`)

**Purpose:** Parse SDN data format (Simple's config/data language)
**Language:** SDN (not Simple)
**Why Separate:** Different syntax, different purpose (data vs code)

**Example:**
```sdn
package:
  name: myproject
  version: 1.0.0

dependencies:
  http: 2.0
```

---

### IR DSL Parser (`src/compiler/irdsl/parser.spl`)

**Purpose:** Parse .irdsl files defining MIR instructions
**Language:** IR DSL (domain-specific language)
**Why Separate:** Defines compiler IR, not user code

**Example:**
```irdsl
instruction Add:
  params: lhs: Value, rhs: Value
  backend: cranelift, interpreter
  description: "Add two values"
```

---

### Predicate Parser (`src/compiler/predicate_parser.spl`)

**Purpose:** Parse predicate expressions for type system
**Language:** Predicate logic sublanguage
**Why Separate:** Specialized type-level expressions

**Example:**
```simple
fn sort<T where T: Ord>(items: [T]) -> [T]
#           ^^^^^^^^^^^^^ predicate parser handles this
```

---

### FFI Gen Parser (`src/app/ffi_gen/parser.spl`)

**Purpose:** Extract @Lib annotations and extern declarations
**Language:** Annotation scanning (line-based, no full parse)
**Why Separate:** Simple text scanning tool, not language parsing

**Example:**
```simple
@Lib(rust: "reqwest", version: "0.11")
extern class HttpClient:
    static fn new() -> HttpClient
```

---

## Removed Duplicates (Post-Merge)

### ~~App Parser Lexer~~ (`src/app/parser/lexer.spl`)

**Status:** ❌ REMOVED (merged into `compiler/lexer.spl`)

**What was merged:**
- `pending_tokens` buffer (if needed)
- `force_indentation_depth` feature (if used)
- Any unique token kinds or error messages

**Migration:**
```simple
# Before:
from app.parser.lexer import Lexer

# After:
from compiler.lexer import Lexer
```

---

## Convenience Wrappers (Thin, Not Duplicates)

### Interpreter Parser Wrapper (`src/app/interpreter/parser.spl`)

**Purpose:** Simple API for interpreter to use TreeSitter
**Size:** 65 lines (thin wrapper)
**Status:** ✅ Keep (not a duplicate, just convenience)

**API:**
```simple
struct SimpleParser:
    inner: Option<TreeSitterParser>

impl SimpleParser:
    static fn new() -> SimpleParser
    fn parse(source: String) -> Result<Tree, ParseError>
    fn parse_expression(source) -> Result<Tree, ParseError>
    fn parse_statement(source) -> Result<Tree, ParseError>
```

**Why Keep:**
- Thin wrapper (does NOT duplicate parsing logic)
- Provides simple Result-based API for interpreter
- Imports `parser.treesitter.parser.TreeSitterParser` (uses existing code)
- No duplication of tokenization or parsing algorithms

---

## File Organization

### Post-Merge Structure

```
src/
├── compiler/                    ← Core language parsing
│   ├── lexer.spl               (1,268 L) ✅ CANONICAL Simple lexer
│   ├── lexer_types.spl         Token type definitions
│   ├── parser.spl              (1,813 L) ✅ CANONICAL Simple parser
│   ├── parser_types.spl        AST type definitions
│   ├── treesitter.spl          (1,444 L) ✅ CANONICAL outline parser
│   ├── treesitter_types.spl    Outline type definitions
│   ├── parser/
│   │   └── treesitter.spl      (509 L) ✅ KEEP (lightweight IDE mode)
│   ├── predicate_parser.spl    (251 L) ✅ Predicate sublanguage
│   └── irdsl/
│       └── parser.spl          (147 L) ✅ IR DSL parser
│
├── std/
│   └── sdn/                     ← SDN format parsing
│       ├── lexer.spl           (411 L) ✅ SDN lexer
│       └── parser.spl          (683 L) ✅ SDN parser
│
└── app/
    ├── interpreter/
    │   └── parser.spl          (65 L) ✅ TreeSitter wrapper (convenience)
    ├── depgraph/
    │   └── parser.spl          (271 L) ✅ Import scanner (tool)
    ├── ffi_gen/
    │   └── parser.spl          (310 L) ✅ Annotation scanner (tool)
    └── test_runner_new/
        └── test_db_parser.spl  (267 L) ✅ Test DB parser (tool)
```

### What Was Removed

```
src/app/parser/
└── lexer.spl                   (1,654 L) ❌ DELETED (merged → compiler/lexer.spl)
```

---

## Usage Examples

### Example 1: Full Compilation (Compiler)

```simple
# Full two-pass parsing for compiler
use compiler.parser.{Parser}
use compiler.treesitter.{TreeSitter}

fn compile(source: text) -> Module:
    # Pass 1: Get outline (fast)
    val ts = TreeSitter.new(source)
    val outline = ts.parse_outline()

    # Check for outline errors
    if outline.errors.?:
        for err in outline.errors:
            print "Outline error: {err}"

    # Pass 2: Parse full bodies
    val parser = Parser.with_resolved_blocks(source, outline)
    val module = parser.parse_full()

    module
```

---

### Example 2: Quick Outline (LSP/IDE)

```simple
# Fast outline for IDE features (no full parse)
use compiler.treesitter.{TreeSitter}

fn get_symbols(source: text) -> [Symbol]:
    val ts = TreeSitter.new(source)
    val outline = ts.parse_outline()

    var symbols = []

    # Extract function symbols
    for fn_outline in outline.functions:
        symbols = symbols.push(Symbol(
            name: fn_outline.name,
            kind: SymbolKind.Function,
            line: fn_outline.span.start_line,
            signature: fn_outline.params.map(\p: p.name).join(", ")
        ))

    # Extract class symbols
    for class_outline in outline.classes:
        symbols = symbols.push(Symbol(
            name: class_outline.name,
            kind: SymbolKind.Class,
            line: class_outline.span.start_line
        ))

    symbols
```

---

### Example 3: Tokenization Only (Syntax Highlighting)

```simple
# Just tokenize for syntax highlighting
use compiler.lexer.{Lexer}

fn highlight(source: text) -> [HighlightToken]:
    val lexer = Lexer.new(source)
    val tokens = lexer.tokenize()

    tokens.map(\tok:
        HighlightToken(
            kind: token_kind_to_highlight(tok.kind),
            span: tok.span,
            lexeme: tok.lexeme
        )
    )

fn token_kind_to_highlight(kind: TokenKind) -> HighlightKind:
    match kind:
        case TokenKind.Identifier(_): HighlightKind.Identifier
        case TokenKind.Integer(_): HighlightKind.Number
        case TokenKind.String(_): HighlightKind.String
        case TokenKind.Fn: HighlightKind.Keyword
        # ... etc
```

---

### Example 4: Interpreter Wrapper (Convenience)

```simple
# Interpreter using thin wrapper
use app.interpreter.parser.{SimpleParser, ParseError}

fn interpret(source: text):
    val parser = SimpleParser.new()
    match parser.parse(source):
        case Ok(tree):
            execute(tree)
        case Err(ParseError.SyntaxError(msg, _)):
            print "Syntax error: {msg}"
        case Err(ParseError.UnsupportedLanguage(lang)):
            print "Unsupported language: {lang}"
```

---

### Example 5: Specialized Parser (SDN Config)

```simple
# Parse SDN config file
use std.sdn.parser.{parse_file}

fn load_config(path: text) -> Config:
    match parse_file(path):
        case Ok(SdnValue.Dict(root)):
            Config(
                name: root["package"]["name"].as_string(),
                version: root["package"]["version"].as_string()
            )
        case Err(e):
            panic "Config parse error: {e}"
```

---

## Testing Strategy

### Unit Tests

**Lexer Tests:**
- `test/lib/std/unit/compiler/lexer_spec.spl` - Lexer unit tests
- Test all token kinds, edge cases, error recovery
- Test indentation tracking, string interpolation, math blocks

**Parser Tests:**
- `test/lib/std/unit/parser/` - Parser unit tests
- Test all AST node types
- Test error recovery, partial parsing

**TreeSitter Tests:**
- `test/lib/std/unit/parser/treesitter_*.spl` - TreeSitter tests
- Test outline extraction
- Test incremental updates (if supported)

### Integration Tests

**Compiler Tests:**
- `test/compiler/` - Full compilation tests
- Test two-pass parsing (outline → full)

**Feature Tests:**
- `test/system/features/parser/` - Feature specs
- Test all language features end-to-end

### Regression Tests

**After Merge:**
- Run full test suite: `simple test`
- Run Rust tests: `simple build rust test`
- Verify no behavior changes (except intended improvements)

---

## Performance Considerations

### Lexer Performance

**Current:** Lexer is fast (single-pass, character-by-character)

**Optimizations:**
- Use string slicing instead of char-by-char when possible
- Cache frequently used tokens (keywords)
- Lazy-load block registry (already implemented)

### TreeSitter Performance

**Current:** TreeSitter is fast (outline-only, no full bodies)

**Optimizations:**
- Fast mode: Skip Skippable blocks (already implemented)
- Incremental parsing: Reuse unchanged portions (planned)
- Parallel outline parsing: Parse multiple files in parallel (future)

### Parser Performance

**Current:** Parser is slower (full AST construction)

**Optimizations:**
- Two-pass: Use outline to avoid redundant parsing (already implemented)
- Lazy body parsing: Parse bodies on-demand (future)
- Parallel parsing: Parse function bodies in parallel (future)

---

## Error Handling Strategy

### Lexer Errors

**Strategy:** Emit `TokenKind.Error(message)` and continue
**Recovery:** Skip to next valid token boundary (newline, delimiter)

**Example:**
```simple
val source = "val x = 123.45.67"  # Invalid number
val lexer = Lexer.new(source)
val tokens = lexer.tokenize()
# → [Val, Identifier("x"), Equals, Error("Invalid number: 123.45.67"), Eof]
```

### TreeSitter Errors

**Strategy:** Collect errors in `OutlineModule.errors`, continue parsing
**Recovery:** Skip to next top-level declaration

**Example:**
```simple
val source = "fn foo(x: Int  # Missing closing paren\nfn bar() -> Int: 42"
val ts = TreeSitter.new(source)
val outline = ts.parse_outline()
# outline.errors = [ParseError.UnexpectedEof("Expected ')'")]
# outline.functions = [bar] (foo is skipped due to error)
```

### Parser Errors

**Strategy:** Collect errors in `Parser.errors`, use outline for recovery
**Recovery:** If function body fails, use outline signature and empty body

**Example:**
```simple
val source = "fn foo(x: Int) -> Int: x ++ y"  # Invalid operator
val parser = Parser.new(source)
val module = parser.parse()
# module has foo with signature, but body parsing error recorded
```

---

## Future Enhancements

### 1. Incremental Parsing (LSP)

**Goal:** Reuse unchanged portions when editing

**Implementation:**
```simple
class IncrementalParser:
    tree: OutlineModule
    source: text

    me apply_edit(range: EditRange, new_text: text) -> OutlineModule:
        # Identify affected range in outline
        # Re-parse only affected functions/classes
        # Reuse unchanged portions
```

**Benefit:** Fast LSP response (re-parse only edited function)

---

### 2. Parallel Parsing

**Goal:** Parse multiple files in parallel

**Implementation:**
```simple
fn compile_parallel(files: [text]) -> [Module]:
    files.parallel_map(\file:
        val source = read_file(file)
        val parser = Parser.new(source)
        parser.parse()
    )
```

**Benefit:** Faster multi-file compilation

---

### 3. Error Region Detection

**Goal:** Better LSP error highlighting

**Implementation:**
```simple
struct ErrorRegion:
    line, column, end_line: i64
    message: text
    severity: ErrorSeverity

enum ErrorSeverity:
    Error, Warning, Info
```

**Benefit:** IDE shows error squiggles in exact locations

---

### 4. Syntax Highlighting API

**Goal:** Fast syntax highlighting without full parsing

**Implementation:**
```simple
fn highlight(source: text, range: Range?) -> [HighlightSpan]:
    val lexer = Lexer.new(source)
    val tokens = lexer.tokenize()

    # Filter to range if specified
    if range.?:
        tokens = tokens.filter(\tok: tok.span in range.unwrap())

    tokens.map(\tok: HighlightSpan(
        span: tok.span,
        kind: token_kind_to_highlight(tok.kind)
    ))
```

**Benefit:** Fast syntax highlighting for editors

---

## Migration Checklist

### Phase 1: Preparation

- [x] Audit all parser/lexer/treesitter files
- [x] Create duplication analysis document
- [x] Create architecture design document
- [ ] List all imports of duplicate lexer
- [ ] Identify unique features to migrate

### Phase 2: Lexer Merge

- [ ] Copy unique features from `app/parser/lexer.spl`
- [ ] Update all imports: `app.parser.lexer` → `compiler.lexer`
- [ ] Run tests: `simple test --tag=lexer`
- [ ] Delete `src/app/parser/lexer.spl`
- [ ] Update documentation

### Phase 3: Verification

- [ ] Run full test suite
- [ ] Run Rust tests
- [ ] Check compiler build
- [ ] Verify LSP/IDE features (if applicable)

### Phase 4: Documentation

- [ ] Update file tree documentation
- [ ] Update architecture documentation
- [ ] Add comments explaining canonical files
- [ ] Create migration guide for contributors

---

## Success Criteria

✅ **Single Source of Truth:**
- Only one Simple lexer: `compiler/lexer.spl`
- Only one Simple parser: `compiler/parser.spl`
- Only one Simple outline parser: `compiler/treesitter.spl`

✅ **Clear Separation:**
- Specialized parsers clearly documented as domain-specific
- No confusion between core language parsing and tool parsing

✅ **Reusability:**
- Compiler, interpreter, LSP, tools all use same core components
- Convenience wrappers allowed, but clearly documented

✅ **Testing:**
- All tests pass after merge
- No regressions in behavior
- Performance maintained or improved

✅ **Documentation:**
- Architecture clearly documented
- File organization explained
- Usage examples provided

---

## Appendix: Import Patterns

### Canonical Imports (Post-Merge)

```simple
# Lexer
use compiler.lexer.{Lexer, Token, TokenKind, Span}

# Parser
use compiler.parser.{Parser, Module, Function, Class}

# TreeSitter
use compiler.treesitter.{TreeSitter, OutlineModule}

# Types
use compiler.parser_types.*  # All AST types
use compiler.treesitter_types.*  # All outline types
use compiler.lexer_types.*  # All token types
```

### Specialized Imports

```simple
# SDN parsing
use std.sdn.parser.{parse, parse_file}
use std.sdn.lexer.{Lexer as SdnLexer}

# IR DSL parsing
use compiler.irdsl.parser.{IrDslParser}

# Predicate parsing
use compiler.predicate_parser.{PredicateParser}
```

### Convenience Wrappers

```simple
# Interpreter wrapper
use app.interpreter.parser.{SimpleParser, ParseError}
```

---

**Status:** ✅ Design Complete - Ready for implementation

**Next Steps:**
1. Get user approval for architecture
2. Begin Phase 1: Lexer merge
3. Update documentation
4. Verify all tests pass
