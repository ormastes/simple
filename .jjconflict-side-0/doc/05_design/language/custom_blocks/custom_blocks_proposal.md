# Custom Blocks Specification

**Status:** Proposal
**Date:** 2026-01-15
**Related:** `brevity_syntax_proposal.md`, `ll1_migration_2026-01-11.md`

## Overview

Custom Blocks provide a mechanism to embed domain-specific languages (DSLs) inside Simple source code while preserving:

- **LL(1)-friendly parsing** - One-pass top-level parsing
- **Deterministic semantics** - No "execute raw text" ambiguities
- **Tooling support** - Formatter, IDE, tree-sitter compatible
- **Cross-platform execution** - Notably `sh{}` runs on all platforms

### Standard Block Kinds

| Block | Purpose | Returns |
|-------|---------|---------|
| `m{}` | Mathematics (LaTeX-like input) | `std.math.Expr` |
| `sh{}` | Portable shell scripting | `std.shell.Result` |
| `sql{}` | SQL queries (dialect-tagged) | `std.sql.Query` |
| `re{}` | Regular expressions | `std.regex.Pattern` |
| `md{}` | Markdown documents | `std.doc.Markdown` |
| `html{}` | HTML content | `std.doc.Html` |
| `graph{}` | Diagrams (Mermaid/DOT) | `std.graph.Diagram` |
| `img{}` | Image embedding/generation | `std.media.Image` |

---

## 1. Syntax

### 1.1 Block Expression Forms

**Inline form:**
```simple
val expr = m{ \frac{a}{b} }
val result = sh{ echo "hello" }
```

**Indented form:**
```simple
val query = sql:
    dialect: postgres
    SELECT * FROM users WHERE id = :id
```

### 1.2 Grammar

```ebnf
Expr      ::= ... | BlockExpr
BlockExpr ::= BlockKind '{' BlockPayload '}'

Stmt      ::= ... | BlockStmt
BlockStmt ::= BlockKind ':' NEWLINE INDENT BlockLines DEDENT

BlockKind ::= IDENT
```

### 1.3 Payload Capture Rules

The outer lexer/parser captures `BlockPayload` **without interpreting it as Simple tokens**.

**Brace form `kind{ ... }`:**
- Payload supports nested braces (balanced)
- Strings and escapes are block-defined
- Outer parser only balances braces
- Payload can be empty

**Indent form `kind: ...`:**
- Payload is raw text of indented region
- Preserves newlines
- `DEDENT` ends the payload

### 1.4 LL(1) Analysis

**Key insight:** Block kind is always an identifier followed by `{` or `:`.

```
IDENT followed by:
  '{'  → Block expression, capture until balanced '}'
  ':'  → Block statement, capture indented lines
  other → Not a block (regular identifier)
```

**Single token lookahead:** LL(1) compatible

---

## 2. Compilation Pipeline

Custom blocks compile in phases:

1. **Outer parse** - Produces `BlockNode(kind, payload, span)` without parsing payload
2. **Block resolution** - Maps `kind` to registered block handler
3. **Block parse** - Handler parses payload into Block AST
4. **Validation/typing** - Handler produces typed IR and diagnostics
5. **Lowering/codegen** - IR lowers to runtime calls or compile-time constants

This guarantees that block payloads **never execute as raw text**.

---

## 3. Block Handler Interface

Each block handler provides:

```simple
trait BlockHandler:
    val kind: str

    fn parse(payload: str, ctx: BlockContext) -> Result<BlockValue, Diagnostics>

    # Optional
    fn format(payload: str) -> str
    fn highlight(payload: str) -> List<Token>
    fn emit_assets(value: BlockValue) -> List<AssetRef>
    fn eval_compile_time(value: BlockValue) -> Option<ConstValue>
```

### 3.1 Determinism Constraints

By default, block parsing and validation must be:
- Deterministic
- Side-effect free
- No network access
- No filesystem writes

Exceptions require explicit package configuration (see Section 11).

---

## 4. Standard Blocks

### 4.1 `m{}` - Math Block

**Purpose:** Human-friendly math entry with semantic IR output.

**Type:** `std.math.Expr`

#### Supported Input Styles

**LaTeX-like operators:**
```simple
val f = m{ \frac{a}{b} }           # Fraction
val r = m{ \sqrt{x} }              # Square root
val p = m{ x^2 }                   # Power
val s = m{ \sum_{i=0}^{n} i }      # Summation
val i = m{ \int_{0}^{1} x dx }     # Integral
val g = m{ \alpha + \beta }        # Greek letters
```

**ASCII aliases:**
```simple
val f = m{ frac(a, b) }
val r = m{ sqrt(x) }
val s = m{ sum(i:Nat, 0..n) i }
val i = m{ int(x:Real, 0..1) x dx }
```

#### Implicit Multiplication

Within `m{}`, adjacency implies multiplication:

```simple
m{ 2x }            # 2 * x
m{ 3(x+1) }        # 3 * (x+1)
m{ (x+1)(x-1) }    # (x+1) * (x-1)
m{ \pi r^2 }       # pi * r^2
```

**Rules:**
- `ab` is a single variable named `ab`
- `a b` (space-separated) becomes `a * b`
- `f(x)` is function application, not multiplication

#### Rendering

```simple
val expr = m{ \frac{1}{1+x} }
val latex = std.math.render(expr, "latex")
val mathml = std.math.render(expr, "mathml")
val lean = std.math.render(expr, "lean")  # Requires explicit typing
```

---

### 4.2 `sh{}` - Portable Shell Block

**Purpose:** Bash-like syntax with OS-neutral execution.

**Type:** `std.shell.Result { stdout: Bytes, stderr: Bytes, status: i32 }`

**Key feature:** NOT executed by `/bin/sh` or `cmd.exe`. Runs consistently on Windows/macOS/Linux.

#### Syntax

```simple
val r = sh{
    mkdir -p out
    cp src/app out/
    echo "done"
}

if r.status != 0:
    panic(r.stderr.to_str())
```

#### Pipes and Redirects

```simple
val r = sh{ cat file | grep foo > out.txt }
```

#### Variables

```simple
val r = sh{
    NAME=world
    echo "hello $NAME"
}
```

**Note:** Interpolation is `$VAR` only. No `eval`.

#### Built-in Portable Commands

| Command | Description |
|---------|-------------|
| `cp` | Copy files |
| `mv` | Move/rename files |
| `rm` | Remove files |
| `mkdir` | Create directories |
| `echo` | Print text |
| `cat` | Concatenate files |
| `exists` | Check file exists |
| `files` | List files |

---

### 4.3 `sql{}` - SQL Block

**Purpose:** Embed SQL with typed parameters and dialect support.

**Type:** `std.sql.Query`

#### Syntax

```simple
val q = sql{
    dialect: postgres
    SELECT id, name FROM users WHERE id = :id
}

db.query(q, { id: user_id })
```

#### Parameter Markers

| Marker | Type |
|--------|------|
| `:name` | Named parameter |
| `?` | Positional parameter |

#### Dialect Selection

```simple
val q = sql{
    dialect: postgres|mysql|sqlite|ansi
    ...
}
```

If omitted: uses project default from `__init__.spl`.

---

### 4.4 `re{}` - Regular Expression Block

**Purpose:** Compiled regex without string escaping noise.

**Type:** `std.regex.Pattern`

#### Syntax

```simple
val p = re{
    (?P<user>[a-zA-Z_]\w*)@(?P<host>[\w.]+)
}

val m = p.match(s)
if m:
    val user = m.group("user")
    val host = m.group("host")
```

#### Flags

```simple
val p = re{
    flags: i m
    ^hello\s+(?P<name>\w+)$
}
```

| Flag | Meaning |
|------|---------|
| `i` | Case insensitive |
| `m` | Multiline mode |
| `s` | Dot matches newline |
| `x` | Extended (ignore whitespace) |

---

### 4.5 `md{}` - Markdown Block

**Purpose:** Embed Markdown content with sub-block support.

**Type:** `std.doc.Markdown`

#### Syntax

```simple
val doc = md{
    # Title

    This is a paragraph with **bold** and *italic*.

    - Item 1
    - Item 2
}
```

#### Embedding Math

**Inline nested blocks:**
```simple
val doc = md{
    # Equation
    Here is math: ${m{ \frac{1}{1+x} }}.
}
```

**Fenced blocks:**
```simple
val doc = md{
    # Equation

    ```math
    \frac{1}{1+x}
    ```
}
```

---

### 4.6 `html{}` - HTML Block

**Purpose:** Embed HTML content directly.

**Type:** `std.doc.Html`

#### Syntax

```simple
val page = html{
    <div class="container">
        <h1>Title</h1>
        <p>Content with ${m{ x^2 }} math.</p>
    </div>
}
```

---

### 4.7 `graph{}` - Diagram Block

**Purpose:** Embed diagrams with text-based DSL.

**Type:** `std.graph.Diagram { format: str, asset_ref: AssetRef }`

#### Syntax

```simple
val d = graph{
    engine: mermaid
    graph TD
        A-->B
        B-->C
}
```

**Supported engines:**
- `mermaid` - Mermaid.js syntax
- `dot` - Graphviz DOT syntax

#### Embedding in Docs

```simple
val d = graph{
    engine: mermaid
    graph LR
        Parse --> IR --> Render
}

val doc = md{
    ## Pipeline
    ${d}
}
```

---

### 4.8 `img{}` - Image Block

**Purpose:** Embed or generate images.

**Type:** `std.media.Image { format: str, asset_ref: AssetRef }`

#### Embed Existing

```simple
val logo = img{
    from: file "assets/logo.png"
}
```

#### Generate (requires opt-in)

```simple
val hero = img{
    gen:
        prompt: "A clean block diagram of a compiler pipeline"
        size: 1024
        seed: 1234
}
```

**Note:** Generation must be explicitly enabled in package config.

---

## 5. Nested Blocks and Interpolation

Blocks may support interpolation via `${ ... }`:

```simple
val eq = m{ x^2 + y^2 = z^2 }

val doc = md{
    # Pythagorean Theorem
    The equation: ${eq}
}
```

**Rules:**
- Interpolated expression is a normal Simple expression
- Result must implement a render interface for the host block
- Math renders to LaTeX/MathML inside HTML/MD

---

## 6. Error Handling

Block handler errors are **compile-time diagnostics** by default:

| Block | Error Type | Timing |
|-------|------------|--------|
| `m{}` | Parse errors, unknown commands | Compile-time |
| `sql{}` | Parse errors, dialect mismatch | Compile-time |
| `re{}` | Invalid regex | Compile-time |
| `graph{}` | Invalid graph DSL | Compile-time |
| `img{}` | Invalid config | Compile-time |
| `sh{}` | Parse errors | Compile-time |
| `sh{}` | Execution errors | Runtime (status code) |

---

## 7. Deterministic Builds and Caching

Block values are cacheable by:

```
(kind, payload_text, handler_version, config_hash)
```

Generated assets (graphs/images) are keyed by this tuple and stored in build cache.

---

## 8. Dunder Interface for Blocks

Custom blocks integrate with the dunder interface:

```simple
trait __block__<K, R>:
    fn __block__(kind: K, payload: str) -> R
```

This allows user-defined block kinds:

```simple
# Define custom block handler
impl MyDSL:
    fn __block__(kind: "mydsl", payload: str) -> MyAST:
        parse_my_dsl(payload)

# Use custom block
val ast = mydsl{ ... }
```

---

## 9. Formatting and Tooling

Each standard block defines:
- Canonical formatter
- Syntax highlighting tokens
- Diagnostic spans mapped to payload locations

The compiler stores:
- `outer_span` - Location of block in Simple source
- `inner_span` - Line/column mapping inside payload

---

## 10. Implementation Files

**Parser:** `src/parser/src/expressions/blocks.rs` - Block expression parsing
**Handlers:** `src/compiler/src/blocks/` - Block-specific handlers
**Runtime:** `src/runtime/src/value/blocks.rs` - Block value types
**Stdlib:** `simple/std_lib/blocks/` - Standard block implementations

---

## 11. Package Configuration

Custom blocks are configured in `__init__.spl`:

```simple
blocks:
    enable: [m, sh, sql, re, md, html, graph, img]

math:
    implicit_mul:
        num_ident: true
        num_group: true
        group_group: true
        ident_ident: "space"  # off | space | on

sql:
    default_dialect: postgres
    allow_ddl: false

sh:
    allow_external: true
    sandbox:
        fs_write: "package"  # none | package | any
        net: false

graph:
    engine: mermaid
    output: svg

img:
    allow_generation: false  # Must be explicitly enabled
    allow_network_models: false
    output: png
```

---

## 12. Summary: LL(1) Compatibility

| Feature | LL(1) Safe | Mechanism |
|---------|------------|-----------|
| Block expression `kind{...}` | Yes | `IDENT` + `{` triggers block mode |
| Block statement `kind:` | Yes | `IDENT` + `:` + `NEWLINE` triggers block mode |
| Nested braces | Yes | Brace balancing in lexer |
| Interpolation `${...}` | Yes | Recursive descent into Simple parser |

**All block syntax is LL(1)-compatible.**

---

## 13. Non-Goals

- Full Bash compatibility (eval, job control, traps)
- Full LaTeX coverage (custom TeX macros, arbitrary packages)
- Executing raw SQL without parameterization
- Networked/non-deterministic asset generation by default

---

## 14. References

- [LaTeX Math Reference](https://en.wikibooks.org/wiki/LaTeX/Mathematics)
- [MathML Specification](https://www.w3.org/Math/)
- [Mermaid.js Documentation](https://mermaid.js.org/)
- [Graphviz DOT Language](https://graphviz.org/doc/info/lang.html)
- [Python Raw Strings](https://docs.python.org/3/reference/lexical_analysis.html#string-and-bytes-literals)
- [Rust Raw String Literals](https://doc.rust-lang.org/reference/tokens.html#raw-string-literals)
