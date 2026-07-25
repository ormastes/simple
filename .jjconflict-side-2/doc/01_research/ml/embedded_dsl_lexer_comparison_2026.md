# Embedded DSL and Custom Grammar Blocks: Cross-Language Lexer Research

**Date:** 2026-01-31
**Context:** Research for Simple language support for custom grammar blocks like `m{ x^2 }`, `sh{ echo }`, `sql{ SELECT }`, `regex{ \d+ }`, `md{ # heading }`, and diagram DSLs.

---

## Executive Summary

This research examines how 10+ programming languages handle embedded DSLs, custom grammar blocks, and raw string literals. Key findings:

1. **Three Main Approaches:**
   - **Lexer Mode Switching** (Scala XML, Typst math) - Fast but complex state management
   - **Delimiter Customization** (Rust `r#"..."#`, Swift `#"..."#`) - Simple but limited
   - **Token Stream Processing** (Rust macros, Julia string macros) - Most flexible

2. **Best Delimiter Strategy:**
   - **Paired delimiters** (`{}`, `[]`, `()`) require brace counting for nesting
   - **Customizable delimiters** (Rust/Swift `#` multiplier) eliminate escaping entirely
   - **Heredoc-style** (Elixir triple-quotes) best for multi-line content

3. **Performance Implications:**
   - Lexer mode switching: Fast (no token reparsing) but complex state management
   - Token stream approach: Moderate (single-pass lexing, compile-time sub-parsing)
   - String extraction: Slow (runtime parsing) but most flexible

4. **Recommended Approach for Simple:**
   - Use **prefix + balanced delimiters**: `m{ }`, `sh{ }`, `sql{ }`, `regex{ }`, `md{ }`
   - Implement **brace counting** in lexer for nested `{}`
   - Pass **raw content** to domain-specific sub-parsers (no lexer mode switching)
   - Support **escape hatch** with configurable delimiters: `m#{ x{y} }#` when needed

---

## 1. Rust: Macros and Raw Strings

### Delimiter Strategy

**Raw Strings:**
```rust
r"C:\Program Files\"           // r"..."
r#"He said "hello""#           // r#"..."# (contains ")
r##"Raw: r#"nested"#"##        // r##"..."## (contains #)
```

**Macro Invocations:**
```rust
println!("Hello")              // Token tree with ()
vec![1, 2, 3]                  // Token tree with []
macro_rules! example {         // Match arms use {}
    ($x:expr) => { ... }
}
```

### Lexer Implementation

- **Customizable delimiters:** The number of `#` symbols determines when the string ends
- **Token trees:** Macros receive **balanced token trees**, not strings
  - Lexer performs brace matching: `{ ( [ ] ) }` must balance
  - Comments and strings are preserved as tokens
- **Sub-parsing:** Proc macros use `syn` crate to parse Rust syntax from token streams

### Handling Delimiters Inside Blocks

- **Raw strings:** Add more `#` symbols until no conflict: `r###"..."###`
- **Macros:** Braces must balance - lexer counts nesting depth
  - `{ { } }` → depth tracking (0→1→2→1→0)
  - Unbalanced braces cause lexer errors

### Performance

- ✅ **Fast:** Single-pass lexing with delimiter counting
- ✅ **Compile-time:** Macro expansion happens during compilation
- ⚠️ **Trade-off:** Token tree approach means comments/strings inside macros are lexed as Rust tokens

**Sources:**
- [macro_rules! - Rust By Example](https://doc.rust-lang.org/rust-by-example/macros.html)
- [Procedural macros - The Rust Reference](https://doc.rust-lang.org/reference/procedural-macros.html)
- [SE-0200 Enhancing String Literals Delimiters](https://github.com/swiftlang/swift-evolution/blob/main/proposals/0200-raw-string-escaping.md)

---

## 2. Scala: String Interpolation and XML Literals

### Delimiter Strategy

**String Interpolation:**
```scala
s"Hello $name"                 // Simple variable
s"Result: ${x + y}"            // Full expression in ${}
f"Price: $amount%.2f"          // Format string
raw"C:\Users\$name"            // Raw string (no escape)
```

**XML Literals:**
```scala
val xml = <div class="container">
  <p>Hello {name}</p>           // Scala expression in {}
</div>
```

### Lexer Implementation

- **Mode switching:** Lexer switches between Scala mode and XML mode
  - Trigger: `<` preceded by whitespace/`(`/`{` + followed by XML name character
  - Exit: XML expression successfully parsed OR `{` forces Scala mode
- **Stack-based:** Parser maintains stack for nested Scala/XML regions
- **Brace matching:** Newlines disabled between matching `{` and `}` except in nested regions

### Handling Delimiters Inside Blocks

- **String interpolation:** `${...}` can contain arbitrary Scala code (multi-statement blocks)
  - Lexer counts braces to find matching `}`
- **XML mode:** Curly braces `{}` escape back to Scala expressions
  - Stack tracks nesting: XML → Scala → XML → ...

### Performance

- ⚠️ **Complex:** Mode switching with stack management
- ✅ **Elegant:** Seamless integration of XML syntax
- ⚠️ **Trade-off:** Scala 3 dropped XML literals (moved to library)

**Note:** Scala 3 dropped XML literals due to lexer complexity. This suggests mode switching may not be worth the maintenance burden.

**Sources:**
- [Lexical Syntax - Scala 2.13](https://scala-lang.org/files/archive/spec/2.13/01-lexical-syntax.html)
- [Dropped: XML Literals - Scala 3](https://dotty.epfl.ch/docs/reference/dropped-features/xml.html)
- [String Interpolation - Scala 3](https://docs.scala-lang.org/scala3/book/string-interpolation.html)

---

## 3. Kotlin: DSL Builders and String Templates

### Delimiter Strategy

**String Templates:**
```kotlin
"Hello $name"                   // Variable
"Result: ${x + y}"              // Expression
"""Multi-line
   string $variable"""          // Triple-quoted
```

**DSL Builders:**
```kotlin
html {
    body {
        div {
            +"Hello"             // Unary plus for strings
        }
    }
}
```

### Lexer Implementation

- **No special lexer support:** DSLs use Kotlin's own grammar
  - Type-safe builders via extension functions + lambdas with receivers
  - All parsing happens with standard Kotlin lexer/parser
- **String templates:** Lexer tracks `$` and `${...}` within strings
  - Simple scan for `}` with brace counting

### Handling Delimiters Inside Blocks

- **String templates:** Braces inside `${...}` are counted
  - `"${map["key"]}"` → lexer counts `{` and `}` to find end
- **Triple-quoted strings:** No escaping needed (but can't contain `"""`)
- **DSLs:** Regular Kotlin syntax - braces matched by parser

### Performance

- ✅ **Simple:** No lexer modes or special tokens
- ✅ **Reusable:** DSL syntax is just Kotlin code
- ⚠️ **Verbose:** Requires `{}` for all DSL blocks

**Sources:**
- [Type-safe builders - Kotlin Documentation](https://kotlinlang.org/docs/type-safe-builders.html)
- [Lixy: A Kotlin lexer framework](https://github.com/utybo/Lixy)
- [Kotlin DSL: from Theory to Practice](https://www.jmix.io/cuba-blog/kotlin-dsl-from-theory-to-practice/)

---

## 4. Swift: Raw Strings and String Interpolation

### Delimiter Strategy

**Raw Strings with Custom Delimiters:**
```swift
"Normal: \(value)"              // Interpolation
#"Raw: \(no interpolation)"#    // One pound sign
##"Raw: \#(interpolates)"##     // Two pound signs
###"Regex: \d+{3}"###           // Three pound signs
```

### Lexer Implementation

- **Customizable escape delimiter:** Use `#` symbols to control interpretation
  - String starts with `"` or `#"` or `##"` etc.
  - Escape delimiter must match: `\#(...)` for `#"..."#`
  - Lexer counts `#` symbols at start to determine required ending
- **Implementation:** Changes confined to `lib/Parse/Lexer.cpp`

### Handling Delimiters Inside Blocks

- **No conflict possible:** Add more `#` symbols until content doesn't contain that pattern
  - `#"\#(interpolates)"#` can contain `\(` literally
  - `##"Contains #"#"##` can contain `#"..."#`
- **Rust-inspired:** Borrowed Rust's customizable delimiter approach

### Performance

- ✅ **Fast:** Simple delimiter counting (no mode switching)
- ✅ **Flexible:** Supports both raw and interpolated in same syntax
- ✅ **Clean:** Inherited Rust's proven design

**Sources:**
- [SE-0200: Raw String Escaping](https://github.com/swiftlang/swift-evolution/blob/main/proposals/0200-raw-string-escaping.md)
- [Behind SE-0200](https://www.swift.org/blog/behind-SE-0200/)
- [How to use raw strings in Swift 5](https://www.hackingwithswift.com/articles/162/how-to-use-raw-strings-in-swift)

---

## 5. Julia: Non-Standard String Literals

### Delimiter Strategy

**String Macros:**
```julia
r"regex: \d+"                   // Regex (no escaping needed)
b"byte array"                   // Byte array
v"1.2.3"                        // Version number
ip"192.168.1.1"                 // IP address
html"<div>$var</div>"           // Custom macro (hypothetical)
```

### Lexer Implementation

- **Naming convention:** Prefix + `"..."` calls `@prefix_str` macro
  - `xyz"content"` → `@xyz_str("content")`
  - Macro receives raw string content at compile time
- **No interpolation:** Standard Julia interpolation `$var` doesn't work in non-standard literals
  - Macro must implement its own interpolation if needed
- **Delimiter options:** Triple-quoted for multi-line

### Handling Delimiters Inside Blocks

- **Escaping required:** Inside `r"..."`, must escape `"` as `\"`
  - Standard escape rules apply
- **Triple-quotes:** Can use `"""..."""` for multi-line
  - No escaping needed unless content contains `"""`
- **Proposal for paired delimiters:** `⟪content⟫` with no escape mechanism (nested pairs allowed)

### Performance

- ✅ **Compile-time:** Macro expansion during compilation
- ⚠️ **Limitation:** Can't have both parser-supported interpolation AND custom literals
  - "You can have full-blown parser-supported string interpolation or custom string literals, but not both"

**Sources:**
- [Metaprogramming - Julia Language](https://docs.julialang.org/en/v1/manual/metaprogramming/)
- [StringLiterals.jl](https://github.com/JuliaString/StringLiterals.jl)
- [String literal syntax using paired Unicode delimiters](https://github.com/JuliaLang/julia/issues/38948)

---

## 6. Haskell: Quasiquoters

### Delimiter Strategy

**Quasiquoter Syntax:**
```haskell
[quoter| content goes here |]
[sql| SELECT * FROM users WHERE id = ${userId} |]
[regex| \d+{3,5} |]
[here| Multi-line
       content |]
```

**Custom Delimiters:**
```haskell
-- PyF library with custom delimiters
[fmtWith|delimiters=('@','!')|
  Hello @user!, you have !count! messages
|]
```

### Lexer Implementation

- **Template Haskell:** Quasiquoter is a function `String -> Q Exp`
  - Invoked with syntax: `[name| ... |]`
  - Content between `|` and `|]` passed as string
- **Antiquotation:** Many quasiquoters use `${...}` or similar for Haskell expressions
  - `${haskell_expr}` extracts back to Haskell
- **Parser choice:** Commonly uses Parsec for custom parsing

### Handling Delimiters Inside Blocks

- **Fixed delimiters:** Standard `[name| ... |]` - must escape `|]` if it appears in content
- **Custom delimiters:** Libraries like PyF allow configuration:
  - `delimiters = ('@','!')` changes markers from `${}` to `@...!`
  - Avoids conflicts with content

### Performance

- ✅ **Compile-time:** Quasiquoter runs during compilation
- ✅ **Flexible:** Can parse any syntax with Parsec or other parsers
- ⚠️ **Complexity:** Requires Template Haskell (compile-time metaprogramming)

**Sources:**
- [Quasiquotation - HaskellWiki](https://wiki.haskell.org/Quasiquotation)
- [Quasiquotation 101 - School of Haskell](https://www.schoolofhaskell.com/user/marcin/quasiquotation-101)
- [PyF: Haskell QuasiQuoter](https://github.com/guibou/PyF)

---

## 7. Elixir: Sigils and Heredocs

### Delimiter Strategy

**Sigils:**
```elixir
~r/regex: \d+/                  // Regex with /
~r|regex: \d+|                  // Regex with |
~r"regex: \d+"                  // Regex with "
~r'regex: \d+'                  // Regex with '
~r(regex: \d+)                  // Regex with ()
~r[regex: \d+]                  // Regex with []
~r{regex: \d+}                  // Regex with {}
~r<regex: \d+>                  // Regex with <>
```

**Heredocs:**
```elixir
~s"""
Multi-line string
with #{interpolation}
"""
```

### Lexer Implementation

- **Sigil pattern:** Tilde `~` + letter + delimiter
  - Lowercase letter: no interpolation/escaping
  - Uppercase letter: interpolation and escaping enabled
  - 8 delimiter options to avoid escaping
- **Paired delimiters:** Lexer function maps opening to closing:
  ```erlang
  sigil_terminator($() -> $);
  sigil_terminator($[) -> $];
  sigil_terminator(${) -> $};
  sigil_terminator($<) -> $>;
  sigil_terminator(O) -> O.  % Self-terminating
  ```
- **Recursive matching:** `extract/8` function scans for terminator, tracks nesting

### Handling Delimiters Inside Blocks

- **Choose delimiter wisely:** Use `~r/regex/` if regex contains `"` and `'`
- **Paired delimiters:** Automatically handle nesting
  - `~r{outer {inner} text}` works because lexer counts braces
- **Heredocs:** Triple-quotes for multi-line (no escaping unless `"""` appears)

### Performance

- ✅ **Fast:** Single-pass lexing with delimiter matching
- ✅ **Ergonomic:** 8 delimiter choices minimize escaping
- ✅ **Simple:** No mode switching (just delimiter tracking)

**Sources:**
- [Sigils - Elixir Programming Language](https://hexdocs.pm/elixir/sigils.html)
- [elixir_tokenizer.erl](https://github.com/elixir-lang/elixir/blob/main/lib/elixir/src/elixir_tokenizer.erl)
- [elixir_interpolation.erl](https://github.com/elixir-lang/elixir/blob/main/lib/elixir/src/elixir_interpolation.erl)

---

## 8. Ruby: Heredocs and Percent Literals

### Delimiter Strategy

**Heredocs:**
```ruby
<<HEREDOC
Content here
HEREDOC

<<~HEREDOC                      // Squiggly heredoc (strips indent)
  Indented content
HEREDOC
```

**Percent Literals:**
```ruby
%w{array of words}              // String array
%r{regex: \d+}                  // Regex
%Q{interpolated "string"}       // Double-quoted behavior
%q{literal 'string'}            // Single-quoted behavior
```

### Lexer Implementation

- **Heredoc:** Start marker `<<IDENTIFIER` on one line, content until line starts with `IDENTIFIER`
  - Delimiter is the entire identifier (e.g., `HEREDOC`, `SQL`, `END`)
  - Content can contain any characters
- **Percent literals:** `%` + letter + delimiter
  - Can use most non-alphanumeric characters as delimiters
  - Brackets recommended for visual clarity

### Handling Delimiters Inside Blocks

- **Heredoc:** Terminator must appear at line start - no escaping needed for content
  - Can't have a line starting with the terminator identifier
- **Percent literals:** Paired brackets allow nesting
  - `%w{outer {nested} words}` works
  - Other delimiters require escaping

### Performance

- ✅ **Simple:** Line-based scanning for heredocs
- ✅ **Flexible:** Many delimiter options for percent literals
- ⚠️ **Quirk:** Heredoc terminator must be at line start (column 0 or after indent for `<<~`)

**Sources:**
- [literals.rdoc - Ruby 2.5.0](https://ruby-doc.org/core-2.5.0/doc/syntax/literals_rdoc.html)
- [Percent notation in Ruby](https://deepsource.com/blog/ruby-percent-notation)
- [literals - Documentation for Ruby 3.2](https://docs.ruby-lang.org/en/3.2/syntax/literals_rdoc.html)

---

## 9. Raku (Perl 6): Grammars and Slangs

### Delimiter Strategy

**Slangs (Sublanguages):**
```raku
use v5;                         // Switch to Perl 5 mode
# Perl 5 code here

# Back to Raku
```

**Grammars:**
```raku
grammar SQL {
    token TOP { <select> | <insert> | <update> }
    token select { 'SELECT' <columns> 'FROM' <table> }
    # ... more rules
}

# Use the grammar
my $parsed = SQL.parse($sql_string);
```

### Lexer Implementation

- **Self-hosting:** Raku's own grammar is written in Raku (`Perl6::Grammar`)
- **Slang switching:** Module provides grammar + actions
  - Grammar parses source code
  - Actions translate to AST (Abstract Syntax Tree)
  - Compiler handles mapping AST to backend (Parrot, JVM, etc.)
- **Context-sensitive parsing:** Rules offer PEG-like capabilities

### Handling Delimiters Inside Blocks

- **Grammar-based:** Delimiters defined by grammar rules
  - Arbitrary complexity supported (context-free and beyond)
- **Slang compilation:** Compiles to QAST (Rakudo's AST format)
  - Language switcher only needs to translate foreign code to known AST

### Performance

- ✅ **Powerful:** Can parse any language (even Perl 5 inside Raku)
- ⚠️ **Complex:** Requires full grammar definition
- ✅ **Extensible:** New slangs can be added by users

**Note:** Raku demonstrates the ultimate in extensibility but requires significant infrastructure. Probably overkill for most use cases.

**Sources:**
- [Raku (programming language) - Wikipedia](https://en.wikipedia.org/wiki/Raku_(programming_language))
- [A Review of Perl 6 (Raku)](https://www.evanmiller.org/a-review-of-perl-6.html)
- [Day 16 – Slangs - Raku Advent Calendar](https://perl6advent.wordpress.com/2013/12/16/day-16-slangs/)

---

## 10. Tree-sitter: Language Injection

### Delimiter Strategy

**Language Injection:**
```javascript
// tree-sitter recognizes patterns:
const html = `<div>${expr}</div>`;        // HTML in template literal
const regex = /\d+/;                      // Regex literal
/* SQL */ const query = `SELECT * FROM`;  // Magic comment
```

### Lexer Implementation

- **Parent + injected trees:** Main syntax tree contains nodes where injected languages reside
  - HTML file: JavaScript in `<script>`, CSS in `<style>`
  - ERB: Ruby in `<% %>`
  - JavaScript: regex inside `/...../`, template literals
- **Injection queries:** Run over entire buffer to find injection points
  - Can be slow for large buffers
  - Can be disabled per-language
- **Included ranges:** Parser can be configured with specific byte ranges
  - Parse each embedded section independently

### Handling Delimiters Inside Blocks

- **Language-specific:** Each language's grammar handles its own delimiters
- **Incremental parsing:** Tree-sitter efficiently updates when edits occur
  - Only re-parses affected regions

### Performance

- ✅ **Incremental:** Only re-parse changed sections
- ⚠️ **Setup cost:** Injection queries scan entire buffer
- ✅ **Editor-optimized:** Designed for syntax highlighting in editors

**Sources:**
- [Using Parsers - Tree-sitter](https://tree-sitter.github.io/tree-sitter/using-parsers/)
- [Tree Sitter and Parsing Languages](https://www.masteringemacs.org/article/tree-sitter-complications-of-parsing-languages)
- [Parsing multiple-language documents](https://github.com/tree-sitter/tree-sitter/discussions/793)

---

## Special Cases: Math, Diagrams, and Templates

### Typst and KaTeX: Math Mode

**Typst:**
```typst
This is text with $x^2$ inline math.

$ x^2 + y^2 = z^2 $              // Display math (spaces matter)
```

**Lexer Implementation:**
- **Whitespace-based:** `$ ... $` with leading/trailing space = display mode
  - `$x^2$` = inline, `$ x^2 $` = display
- **Mode switching:** Lexer switches between markup, math, and code modes
  - Use `#` to escape to code mode inside math
- **Three modes:** Markup (default), Math (`$...$`), Code (`#...`)

**Sources:**
- [Math - Typst Documentation](https://typst.app/docs/reference/math/)
- [Guide for LaTeX users](https://typst.app/docs/guides/guide-for-latex-users/)
- [Syntax - Typst Documentation](https://typst.app/docs/reference/syntax/)

---

### MDX: Markdown + JSX

**Syntax:**
```mdx
# Markdown heading

<CustomComponent prop={value}>
  Markdown content here
</CustomComponent>

```javascript
// Code block with syntax highlighting
const x = 42;
\```
```

**Lexer Implementation:**
- **Challenge:** Determining Markdown vs JSX regions
  - No clear "signatures" for Markdown blocks
  - `{}` for JSX, `<>` for tags, but also in generics
- **Workaround:** Require blank lines around Markdown syntax
  - Parser uses whitespace to disambiguate
- **Code blocks:** Contain JSX → no parsing (treated as plain text)

**Sources:**
- [MDX: Markdown for the component era](https://mdxjs.com/)
- [Making the text editor syntax-file](https://github.com/orgs/mdx-js/discussions/2301)
- [Option to ignore jsx in code blocks](https://github.com/mdx-js/mdx/issues/2074)

---

### Mermaid, PlantUML, D2: Diagram Languages

**Embedding Approach:**
```markdown
```mermaid
graph TD
    A[Start] --> B[Process]
    B --> C[End]
\```

```plantuml
@startuml
Alice -> Bob: Hello
@enduml
\```

```d2
x -> y: Connection
\```
```

**Implementation:**
- **Code fence:** Standard Markdown code blocks with language identifier
  - ` ```mermaid ... ``` `
  - No special lexer support needed
- **Rendering:** External tools process the diagram DSL
  - Mermaid: JavaScript (browser-based)
  - PlantUML: Java (server-side)
  - D2: Go (CLI tool)
- **Advantage:** Auto-rendering in GitHub, GitLab, documentation tools

**Sources:**
- [Include diagrams in Markdown with Mermaid](https://github.blog/developer-skills/github/include-diagrams-markdown-files-mermaid/)
- [LinkORB: Use Mermaid.js and PlantUML](https://engineering.linkorb.com/topics/markdown/articles/mermaid-plantuml/)
- [Text to Diagram Tools Comparison 2025](https://text-to-diagram.com/?example=text)

---

### GraphQL: Tagged Template Literals

**Syntax:**
```javascript
const query = gql`
  query GetUser($id: ID!) {
    user(id: $id) {
      name
      email
    }
  }
`;
```

**Lexer Implementation:**
- **Tagged templates:** JavaScript ES6 feature
  - `` tag`content` `` calls `tag(strings, ...values)`
  - No special lexer mode - just normal template literal
- **graphql-tag:** Library that parses GraphQL AST at runtime
  - Can be pre-compiled with `ts-transform-graphql-tag`
- **Type safety:** TypeScript plugins provide GraphQL schema validation

**Sources:**
- [graphql-tag - Apollo](https://github.com/apollographql/graphql-tag)
- [Tagged template literals: how gql\`query\` works](https://pavsaund.com/post/2020-10-26-tagged-template-literals-how-the-gql-query-syntax-works/)
- [ts-graphql-plugin](https://github.com/Quramy/ts-graphql-plugin)

---

## Comparative Analysis Table

| Language | Delimiter Strategy | Escaping Mechanism | Nesting Support | Lexer Approach | Performance |
|----------|-------------------|-------------------|----------------|----------------|-------------|
| **Rust** | `r#"..."#` (customizable `#` count) | Add more `#` | Macro token trees: counted braces | Single-pass with delimiter counting | ✅ Fast |
| **Scala** | `s"${...}"`, `<xml>` | Backslash in strings, `{}` for code | Stack-based mode switching | Mode switching (Scala ↔ XML) | ⚠️ Complex |
| **Kotlin** | `"${...}"`, `"""..."""` | `\` in single-quote strings | Brace counting | Standard lexer (no special modes) | ✅ Simple |
| **Swift** | `#"..."#` (customizable `#` count) | Add more `#` | N/A (strings only) | Delimiter counting | ✅ Fast |
| **Julia** | `prefix"..."` | Standard escaping | Triple-quotes for multi-line | Macro expansion (compile-time) | ✅ Fast |
| **Haskell** | `[quoter\| ... \|]` | Custom per quasiquoter | Custom (e.g., `${...}`) | Template Haskell (compile-time) | ✅ Fast |
| **Elixir** | `~r/.../`, `~r{...}`, `~r"""..."""` | 8 delimiter choices | Paired delimiters counted | Delimiter matching | ✅ Fast |
| **Ruby** | `<<HEREDOC`, `%r{...}` | Line-based for heredoc, paired brackets | Paired delimiters counted | Line scanning / delimiter matching | ✅ Simple |
| **Raku** | Grammars, slangs | Grammar-defined | Full context-sensitive parsing | Grammar-based (QAST compilation) | ⚠️ Complex |
| **Tree-sitter** | Language-specific | Per-language rules | Incremental re-parsing | Injection queries + included ranges | ⚠️ Setup cost |
| **Typst** | `$ ... $` (whitespace matters) | `#` for code mode | Mode switching (markup/math/code) | Mode switching | ⚠️ Moderate |
| **MDX** | Blank lines around Markdown | Standard Markdown/JSX escaping | Whitespace disambiguation | Combined Markdown/JSX parser | ⚠️ Ambiguous |
| **GraphQL (JS)** | `` gql`...` `` | Template literal escaping | `${}` for JS expressions | Standard template literal | ✅ Simple |

---

## Implementation Recommendations for Simple

### Recommended Approach: Prefix + Balanced Delimiters with Brace Counting

**Syntax:**
```simple
m{ x^2 + y^2 }                  // Math block
sh{ echo "Hello $USER" }        // Shell script
sql{ SELECT * FROM users }      // SQL query
regex{ \d+(?:\.\d+)? }          // Regex
md{ # Heading\n\nParagraph }    // Markdown
```

**With Escape Hatch (when content contains `}`):**
```simple
m#{ x{y} }#                     // Use #{ }# when content has }
sh##{ echo "}" }##              // Use ##{ }## for multiple }
```

### Lexer Design

**Step 1: Recognize prefix + delimiter**
- Pattern: `IDENTIFIER` + `{` or `#...#{`
  - `m{` → Math block with `}` terminator
  - `m#{` → Math block with `}#` terminator
  - `sh##{` → Shell block with `}##` terminator

**Step 2: Count braces for nesting**
```rust
fn lex_custom_block(prefix: &str) -> Token {
    let pound_count = count_leading_pounds();  // 0 for `m{`, 1 for `m#{`
    let terminator = "}".to_string() + "#".repeat(pound_count);

    let mut depth = 1;  // Start at depth 1 (opening brace)
    let mut content = String::new();

    loop {
        let ch = next_char();
        if ch == '{' && !at_terminator() {
            depth += 1;
            content.push(ch);
        } else if ch == '}' {
            if peek_matches(&"#".repeat(pound_count)) {
                depth -= 1;
                if depth == 0 {
                    consume_terminator();  // Consume }# or }## etc.
                    break;  // Done
                }
            }
            content.push(ch);
        } else {
            content.push(ch);
        }
    }

    Token::CustomBlock { prefix, content }
}
```

**Step 3: Pass raw content to sub-parser**
- Lexer produces `Token::CustomBlock { prefix: "m", content: "x^2 + y^2" }`
- Parser dispatches to appropriate sub-parser:
  - `m` → Math parser (enables `^` operator, different precedence)
  - `sh` → Shell script validator (or pass to runtime)
  - `sql` → SQL parser (compile-time validation)
  - `regex` → Regex compiler
  - `md` → Markdown renderer

### Why This Design?

**✅ Advantages:**

1. **No lexer mode switching** - Simpler state management
   - Lexer only needs to count braces and track terminator
   - No complex stack of modes

2. **Clear visual boundaries** - Easy to see where blocks start/end
   - `m{ ... }` is visually distinct
   - Syntax highlighting can easily identify blocks

3. **Escape hatch available** - Handle edge cases gracefully
   - `m#{ ... }#` when content contains `}`
   - Can add more `#` as needed: `m##{ ... }##`

4. **Nestable by default** - Brace counting handles nested `{}`
   - `m{ f(x{y}) }` works because lexer counts depth
   - No manual escaping needed for most cases

5. **Compile-time validation** - Sub-parsers run during compilation
   - Math: Type-check dimensions, enable `^` operator
   - SQL: Validate query syntax
   - Regex: Check for errors

6. **Performance** - Single-pass lexing with simple depth tracking
   - No token re-parsing
   - No runtime overhead

**⚠️ Considerations:**

1. **Comments and strings inside blocks** - Passed raw to sub-parser
   - Math block: `m{ x /* comment */ + y }` → Math parser handles `/* */`
   - Shell block: `sh{ echo "}" }` → Works (closing `"` comes before `}`)
   - SQL block: `sql{ SELECT '}' FROM t }` → Works (string contains `}`)

2. **Terminator conflict** - Rare but possible
   - Content contains `}` → Use `m#{ ... }#`
   - Content contains `}#` → Use `m##{ ... }##`
   - Rule: Add enough `#` until no conflict

3. **Error messages** - Need to track offset into custom block
   - Math error at `x ^^ 2` → Report "Math block at line 5, column 3: unexpected ^^"
   - Include original source location

### Alternative Considered: Heredoc Style

**Syntax:**
```simple
m"""
x^2 + y^2
"""

sh"""
echo "Hello"
find . -name "*.txt"
"""
```

**Pros:**
- No escaping needed (can't have `"""` in content)
- Multi-line friendly

**Cons:**
- Verbose for short blocks: `m"""x^2"""` vs `m{ x^2 }`
- Triple-quotes less visually distinct than `{ }`
- Harder to nest: Can't put one `m"""..."""` inside another

**Decision:** Prefix + braces is more concise and nestable.

---

## Best Practices Summary

### Delimiter Selection

1. **For short inline blocks:** Balanced delimiters with prefix
   - `m{ x^2 }`, `regex{ \d+ }`, `sql{ SELECT id }`
   - Fast, concise, visually clear

2. **For multi-line blocks:** Triple-quotes or heredoc
   - ` ```lang ... ``` ` (Markdown code fence style)
   - `lang"""..."""` (Python/Kotlin style)
   - `<<LANG ... LANG` (Ruby heredoc style)

3. **For escape hatch:** Customizable delimiters
   - Rust/Swift `#` multiplier approach
   - `m#{ ... }#`, `m##{ ... }##` etc.

### Lexer Implementation

1. **Avoid mode switching if possible**
   - Simpler state management
   - Easier to implement incremental parsing
   - Exception: When language is self-hosting (like Raku)

2. **Use brace counting for paired delimiters**
   - Track nesting depth with counter
   - Push/pop states for alternating regions

3. **Pass raw content to sub-parsers**
   - Don't try to lex embedded language in main lexer
   - Sub-parser knows the rules better

### Performance Optimization

1. **Single-pass lexing** - Don't re-tokenize content
   - Extract block content as single token
   - Parse at semantic analysis phase

2. **Incremental parsing** - Only re-parse changed blocks
   - Track byte offsets for each custom block
   - Re-run sub-parser only if block edited

3. **Compile-time validation** - Catch errors early
   - Math: Dimension checking
   - SQL: Query validation
   - Regex: Syntax errors

---

## Conclusion

**For Simple language, recommend:**

1. **Primary syntax:** `prefix{ content }`
   - Math: `m{ x^2 + y^2 }`
   - Shell: `sh{ echo hello }`
   - SQL: `sql{ SELECT * FROM users }`
   - Regex: `regex{ \d+(?:\.\d+)? }`
   - Markdown: `md{ # Heading }`

2. **Escape syntax:** `prefix#{ content }#` (add more `#` as needed)
   - Use when content contains unbalanced `}`

3. **Multi-line syntax:** Triple-quotes for large blocks
   - `m"""..."""`, `sh"""..."""` etc.
   - Alternative: Use regular braces (braces don't require line boundaries)

4. **Lexer implementation:**
   - Brace counting with depth tracking
   - No mode switching (pass raw content to sub-parser)
   - Support `#` multiplier for escape hatch

5. **Parser implementation:**
   - Dispatch to domain-specific sub-parsers
   - Validate at compile time
   - Track source locations for error messages

This approach balances simplicity (easy to implement), performance (single-pass lexing), and flexibility (supports nesting and escaping).

---

## References

### Language Documentation

- [Rust Macros - Rust By Example](https://doc.rust-lang.org/rust-by-example/macros.html)
- [Procedural Macros - The Rust Reference](https://doc.rust-lang.org/reference/procedural-macros.html)
- [Scala Lexical Syntax 2.13](https://scala-lang.org/files/archive/spec/2.13/01-lexical-syntax.html)
- [Scala 3 String Interpolation](https://docs.scala-lang.org/scala3/book/string-interpolation.html)
- [Kotlin Type-Safe Builders](https://kotlinlang.org/docs/type-safe-builders.html)
- [Swift SE-0200: Raw String Escaping](https://github.com/swiftlang/swift-evolution/blob/main/proposals/0200-raw-string-escaping.md)
- [Julia Metaprogramming](https://docs.julialang.org/en/v1/manual/metaprogramming/)
- [Haskell Quasiquotation - HaskellWiki](https://wiki.haskell.org/Quasiquotation)
- [Elixir Sigils](https://hexdocs.pm/elixir/sigils.html)
- [Ruby Literals Documentation](https://ruby-doc.org/core-2.5.0/doc/syntax/literals_rdoc.html)
- [Raku Slangs - Advent Calendar](https://perl6advent.wordpress.com/2013/12/16/day-16-slangs/)
- [Tree-sitter Using Parsers](https://tree-sitter.github.io/tree-sitter/using-parsers/)

### Implementation Resources

- [Writing a Lexer in C and C++: Complete Guide for 2026](https://copyprogramming.com/howto/writing-a-lexer-in-c)
- [When Are Lexer Modes Useful?](https://www.oilshell.org/blog/2017/12/17.html)
- [Some Strategies For Fast Lexical Analysis](https://nothings.org/computer/lexing.html)
- [Balanced Delimiter Matching](https://mathcenter.oxford.emory.edu/site/cs171/delimiterMatching/)
- [String Literal - Wikipedia](https://en.wikipedia.org/wiki/String_literal)

### Tool-Specific

- [graphql-tag - Apollo](https://github.com/apollographql/graphql-tag)
- [Typst Math Documentation](https://typst.app/docs/reference/math/)
- [MDX: Markdown for the component era](https://mdxjs.com/)
- [Mermaid in Markdown - GitHub Blog](https://github.blog/developer-skills/github/include-diagrams-markdown-files-mermaid/)
- [Text to Diagram Tools Comparison 2025](https://text-to-diagram.com/?example=text)

---

## Per-DSL Conflict Analysis: What Breaks With Naive Brace Counting

### Current Problem

The current lexer (`rust/parser/src/lexer/identifiers.rs:410-441`) uses naive `{`/`}` depth counting with **zero awareness** of strings, comments, or escapes. This section documents exactly which DSLs break and why.

### Severity Table

| DSL | Breaks? | Severity | Root Cause | Example |
|-----|---------|----------|------------|---------|
| **Shell (sh)** | ✅ YES | **Critical** | `}` in strings, comments, variable expansion | `sh{ echo "}" }` |
| **SQL** | ✅ YES | **Critical** | `}` in string literals, comments | `sql{ SELECT '}' FROM t }` |
| **LaTeX** | ✅ YES | **High** | Nested `{}` for grouping, `\}` escapes | `latex{ \text{hello} }` |
| **Regex** | ✅ YES | **High** | `}` in quantifiers, `\}` literal | `regex{ \d{3} }` |
| **HTML/CSS** | ✅ YES | **High** | CSS braces, JS strings in attributes | `html{ <style>div{color:red}</style> }` |
| **JSON** | ✅ YES | **High** | Nested objects with `}` | `json{ {"a": {"b": 1}} }` |
| **Markdown** | ⚠️ MAYBE | **Low** | Code fences may contain `}` | `md{ \`\`\`js\nobj = {}\n\`\`\` }` |
| **Math (m)** | ⚠️ RARE | **Low** | Set notation `{1,2,3}` (balanced, so usually OK) | `m{ S = {1,2,3} }` |
| **PyTorch DL** | ✅ YES | **Medium** | String args with `}`, dict literals | `dl{ Linear(256, "{out}") }` |
| **D2 Diagrams** | ✅ YES | **Medium** | Nested shape `{}` blocks | `d2{ x: { shape: oval } }` |

### Broken Examples Per DSL

**Shell:**
```simple
# BROKEN: String containing }
sh{ echo "value is }" }          # Lexer sees } inside string as block end

# BROKEN: Comment containing }
sh{ # close brace }              # } in comment terminates block early
echo "hello"
}

# BROKEN: Variable expansion
sh{ echo ${VAR:-default} }       # Unbalanced { from ${...}
```

**SQL:**
```simple
# BROKEN: String literal with }
sql{ SELECT * FROM t WHERE col = '}' }

# BROKEN: Comment with }
sql{ SELECT * FROM t -- filter } WHERE id = 1 }
```

**LaTeX:**
```simple
# Works (balanced): \text{hello} has matching braces
latex{ \frac{x}{y} }             # OK: {x} and {y} are balanced

# BROKEN: \} escape (literal brace in output)
latex{ x \in \{1,2,3\} }        # \} is literal, but lexer counts it
```

**Regex:**
```simple
# BROKEN: Quantifier with }
regex{ \d{3} }                   # {3} adds depth, then } closes too early

# BROKEN: Literal } match
regex{ [}] }                     # Character class with }
```

**Shell (to be added):**
```simple
# BROKEN: Heredoc with }
sh{
cat <<'EOF'
}
EOF
}
```

### Tiered Token Tracking Recommendation

To fix these issues without full sub-lexer complexity, we propose tiered awareness:

#### Tier 1: String + Escape Tracking (~90% of conflicts fixed)

Track these inside custom blocks:
- `"..."` double-quoted strings (skip `}` inside)
- `'...'` single-quoted strings (skip `}` inside)
- `\}` backslash-escaped close brace (skip)

**Fixes:** Shell strings, SQL strings, most JSON, most PyTorch DL

#### Tier 2: Comment Tracking (~97% of conflicts fixed)

Additionally track:
- `//` or `#` line comments (skip to EOL)
- `/* ... */` block comments
- `-- ` SQL-style line comments

**Fixes:** Shell comments, SQL comments, CSS comments

#### Tier 3: Per-DSL Registration (99%+ fixed)

Block handlers register their exotic delimiters:
- Regex: `[...]` character classes (skip `}` inside)
- LaTeX: `\{` and `\}` are literal (don't count)
- Shell: `` `...` `` backtick commands, `$(...)` subshells, heredocs
- Markdown: ` ``` ` code fences (skip everything inside)

### Minimal Universal Token Set

These tokens should be tracked by the **common lexer** for ALL custom blocks:

| Token | Pattern | Action | Why |
|-------|---------|--------|-----|
| Double-quoted string | `"..."` | Skip `}` inside | Universal across all DSLs |
| Single-quoted string | `'...'` | Skip `}` inside | Universal across all DSLs |
| Backslash escape | `\}` | Skip this `}` | Common escape convention |
| Balanced braces | `{ ... }` | Depth counting | Already implemented |

### Does Tiered Tracking Still Allow Effective Parsing?

**Yes.** The tiered tracking does NOT change what the sub-parser receives. Here's why:

1. **Payload is unchanged.** The lexer still captures the full raw text between the opening `{` and closing `}`. Tracking strings/comments only affects *which* `}` terminates the block — it doesn't strip, modify, or tokenize the content.

2. **Sub-parsers are unaffected.** The math sub-lexer (`rust/compiler/src/blocks/math/lexer.rs`) still receives `x^2 + y^2` as raw text. The shell handler still receives `echo "}"` as raw text. They parse it with their own rules.

3. **Performance impact is minimal.** Tier 1 adds only: (a) a boolean `in_string` flag, (b) check for `\` before `}`, (c) check for `"` and `'` toggling. This is 2-3 extra comparisons per character — negligible compared to the character-by-character scan already happening.

4. **No ambiguity introduced.** The common lexer's string tracking uses the same universal conventions (`"..."`, `'...'`, `\`) that every DSL already respects. A DSL that uses `"` for something other than strings (none of our supported DSLs do) would need Tier 3 registration to override.

5. **Escape hatch remains.** For truly exotic cases (heredocs, raw strings with unusual delimiters), the `#` escape hatch (`sh#{ ... }#`) completely bypasses brace counting and works for any content.

**Summary:** Tiered tracking makes the block boundary detection smarter without touching the sub-parsing pipeline. The sub-parsers receive identical payloads — just correctly terminated ones.

---

## Custom Grammar Block Inventory

### Currently Implemented

| Block | Prefix | Lexer | Rust Handler | Simple Def | Status |
|-------|--------|-------|-------------|------------|--------|
| **Math** | `m` | ✅ | ✅ `blocks/math/` | ✅ MathBlockDef | **Complete** |
| **Loss** | `loss` | ✅ | via math | ✅ LossBlockDef | **Complete** |
| **Nograd** | `nograd` | ✅ | via math | ✅ NogradBlockDef | **Complete** |
| **Shell** | `sh` | ✅ | ✅ `blocks/shell.rs` | ✅ ShellBlockDef | **Complete** |
| **SQL** | `sql` | ✅ | ✅ `blocks/sql.rs` | ✅ SqlBlockDef | **Complete** |
| **Regex** | `re` | ✅ | ✅ `blocks/regex.rs` | ✅ RegexBlockDef | **Complete** |
| **JSON** | `json` | ✅ | ❌ | ✅ JsonBlockDef | **Def only** |
| **Markdown** | `md` | ✅ | ❌ | ✅ MarkdownBlockDef | **Def only** |

### Lexer-Only (registered in lexer, no handler)

| Block | Prefix | Lexer | Handler | Notes |
|-------|--------|-------|---------|-------|
| **HTML** | `html` | ✅ | ❌ | Marked "not yet implemented" in mod.rs |
| **Graph** | `graph` | ✅ | ❌ | For diagrams |
| **Image** | `img` | ✅ | ❌ | Image embedding |
| **Lean** | `lean` | ✅ | ❌ | Lean 4 theorem prover |

### Planned (not in code yet)

| Block | Prefix | Use Case | Priority |
|-------|--------|----------|----------|
| **LaTeX** | `latex` or `tex` | Full LaTeX typesetting | Medium |
| **CSS** | `css` | Inline stylesheets | Low |
| **Mermaid** | `mermaid` | Mermaid diagrams | Medium |
| **Graphviz** | `dot` or `graphviz` | Graphviz DOT diagrams | Medium |
| **D2** | `d2` | D2 diagrams | Low |

### Per-Block Problem Analysis (Planned Blocks)

#### `latex{}` / `tex{}` — LaTeX

**Problem tokens:**
- `{}` used extensively for grouping: `\frac{a}{b}`, `\text{hello}`
- `\}` and `\{` are literal brace escapes
- `%` is line comment (not `#` or `//`)
- `$...$` for inline math (nested DSL-in-DSL)

**What breaks with naive counting:** Balanced `{}` is usually fine since LaTeX braces pair up. But `\}` and `\{` are literal braces that should NOT be counted. Also `%` comments can contain `}`.

**Needed:** Tier 1 (strings) + Tier 2 (% comments) + Tier 3 (`\{` and `\}` don't count as depth changes).

**Alternative:** Since `m{}` already handles math, `latex{}` is mainly for full-document LaTeX with `\begin{...}\end{...}` environments. Consider whether `m{}` is sufficient or if separate block is needed.

#### `css{}` — CSS

**Problem tokens:**
- `{}` used for rule blocks: `div { color: red; }`
- Nested `@media { div { ... } }` — balanced, usually OK
- String literals with `}`: `content: "}";`
- Comments: `/* ... */`

**What breaks:** String literals `"}"` and `'}'` inside property values. Comments with `}`.

**Needed:** Tier 1 (strings) + Tier 2 (`/* */` comments). All `{}` are balanced in valid CSS, so depth counting works for structure.

#### `mermaid{}` — Mermaid Diagrams

**Problem tokens:**
- Node labels with `{}`: `A{Decision}` is Mermaid syntax for rhombus nodes
- Quoted labels: `A["text with }"]`
- `%%` line comments

**What breaks:** `A{Decision}` adds unbalanced depth if the label contains no matching pair. `A["text}"]` has `}` in quotes.

**Needed:** Tier 1 (strings) + special: Mermaid uses `{}` as node shape delimiters. Since these are balanced (`A{text}`), naive counting actually works here. Only quoted strings with `}` break.

**Recommendation:** Tier 1 is sufficient. Or use `#` escape: `mermaid#{ ... }#`.

#### `dot{}` / `graphviz{}` — Graphviz DOT

**Problem tokens:**
- `{}` used for subgraphs and node groups: `subgraph { A -> B }`
- Quoted strings: `label="has } brace"`
- HTML labels: `<TABLE>...</TABLE>` can contain `{}`
- `//` and `/* */` comments

**What breaks:** Balanced `{}` is fine (DOT braces always pair). String labels with `}` break. HTML labels can have arbitrary content.

**Needed:** Tier 1 (strings) + Tier 2 (comments). HTML labels (`<...>`) are a Tier 3 concern but rare.

#### `d2{}` — D2 Diagrams

**Problem tokens:**
- `{}` for nested shapes: `x: { shape: oval }`
- Quoted strings: `x: "has }"`
- `#` line comments

**What breaks:** Balanced `{}` is fine. Quoted strings with `}` break. `#` comments with `}` break.

**Needed:** Tier 1 (strings) + Tier 2 (`#` comments).

#### `lean{}` — Lean 4

**Problem tokens:**
- `{}` for anonymous constructors and structures: `⟨a, b⟩` or `{ x := 1 }`
- String literals: `"has }"`
- `--` line comments, `/-  -/` block comments
- Unicode: `∀`, `∃`, `→`, `λ` (no brace conflict)

**What breaks:** Lean `{}` is balanced in valid code. String literals and comments with `}`.

**Needed:** Tier 1 (strings) + Tier 2 (`--` line + `/-  -/` block comments).

### Summary: What Each Planned Block Needs

| Block | Tier 1 (strings) | Tier 2 (comments) | Tier 3 (exotic) | `#` escape fallback |
|-------|:-:|:-:|:-:|:-:|
| `latex` | ✅ | `%` line comments | `\{` `\}` literal braces | ✅ |
| `css` | ✅ | `/* */` block comments | — | ✅ |
| `mermaid` | ✅ | `%%` line comments | — | ✅ |
| `dot`/`graphviz` | ✅ | `//` + `/* */` | HTML labels `<...>` | ✅ |
| `d2` | ✅ | `#` line comments | — | ✅ |
| `lean` | ✅ | `--` + `/- -/` | — | ✅ |

**Observation:** Tier 1 (string tracking) fixes all planned blocks for common cases. Tier 2 comment patterns vary per-DSL but are straightforward to register. The `#` escape hatch covers all remaining edge cases.

### Implementation Priority

1. **Immediate (Tier 1):** Add string + backslash tracking to `scan_custom_block_payload()` — fixes 90% of real-world breakage with ~15 lines of code change
2. **Soon (Tier 2):** Add comment tracking — configurable per block kind (SQL uses `--`, shell uses `#`, others use `//` and `/* */`)
3. **Later (Tier 3):** Registration API for exotic syntax — only needed when specific DSLs report edge cases
4. **Always available:** `#` escape hatch as universal fallback

---

**End of Research Document**
