# Custom Blocks Feature Specification

*Source: `simple/std_lib/test/features/syntax/custom_blocks_spec.spl`*

---

# Custom Blocks Feature Specification

**Feature IDs:** #1090-1098
**Category:** Syntax
**Difficulty:** 4/5
**Status:** Planned

## Overview

Custom Blocks embed domain-specific languages (DSLs) inside Simple source code while preserving
LL(1) parseability, deterministic semantics, and tooling support. Blocks are parsed by dedicated
handlers and produce typed values.

**Standard Block Kinds:**
- `m{}` - Mathematics (LaTeX-like input, semantic IR)
- `sh{}` - Portable shell scripting (Bash-like surface, OS-neutral)
- `sql{}` - SQL queries (dialect-tagged, parameter-safe)
- `re{}` - Regular expressions (compiled, typed captures)
- `md{}` - Markdown documents
- `html{}` - HTML content
- `graph{}` - Diagrams (Mermaid/DOT)
- `img{}` - Image embedding/generation

## Syntax

### Block Expression Forms

```simple
# Inline form
val expr = m{ \frac{a}{b} }
val result = sh{ echo "hello" }

# Indented form
val query = sql:
    dialect: postgres
    SELECT * FROM users WHERE id = :id
```

### Grammar

```
BlockExpr ::= BlockKind '{' BlockPayload '}'
BlockStmt ::= BlockKind ':' NEWLINE INDENT BlockLines DEDENT
```

### LL(1) Compatibility

Block kind is always `IDENT` followed by `{` or `:`. Single token lookahead is sufficient.

## Compilation Pipeline

1. Outer parse: `BlockNode(kind, payload, span)` without parsing payload
2. Block resolution: Map `kind` to registered handler
3. Block parse: Handler parses payload into Block AST
4. Validation/typing: Handler produces typed IR
5. Lowering/codegen: IR lowers to runtime calls

## Math Block - LaTeX-like Input with Semantic IR

    The `m{}` block provides human-friendly math entry similar to LaTeX,
    producing a semantic IR that can be rendered to various formats.

    **Type:** `std.math.Expr`

    **Features:**
    - LaTeX-like operators (`\frac`, `\sqrt`, `\sum`, `\int`)
    - ASCII aliases (`frac(a, b)`, `sqrt(x)`)
    - Implicit multiplication (`2x`, `3(x+1)`)
    - Greek letters (`\alpha`, `\pi`)

Simple arithmetic expressions.

LaTeX-style fractions with `\frac{num}{denom}`.

Square root with `\sqrt{x}`.

Exponentiation with `x^n` syntax.

Number-variable adjacency implies multiplication.

Adjacent parenthesized groups multiply.

Greek letter constants.

Summation notation.

Definite integral notation.

Export math expression as LaTeX string.

Export math expression as MathML.

## Shell Block - Portable Shell Scripting

    The `sh{}` block provides Bash-like syntax with OS-neutral execution.
    Commands are NOT executed by `/bin/sh` or `cmd.exe` - they run consistently
    across Windows, macOS, and Linux.

    **Type:** `std.shell.Result { stdout: Bytes, stderr: Bytes, status: i32 }`

    **Features:**
    - Portable built-in commands (cp, mv, rm, mkdir, echo)
    - Pipes and redirects
    - Block-local variables
    - No shell injection vulnerabilities

Basic echo command.

Pipe output between commands.

Redirect output to file.

Variables scoped to the block.

Portable mkdir command.

Portable cp command.

Failed commands return non-zero status.

Multiple commands execute in sequence.

## SQL Block - Parameterized SQL Queries

    The `sql{}` block embeds SQL with typed parameters and dialect support.
    Parameters prevent SQL injection by using prepared statements.

    **Type:** `std.sql.Query`

    **Features:**
    - Named parameters (`:name`)
    - Positional parameters (`?`)
    - Dialect selection (postgres, mysql, sqlite, ansi)

Named parameter markers.

Positional parameter markers.

PostgreSQL-specific syntax.

MySQL-specific syntax.

SQLite-specific syntax.

Invalid SQL produces compile-time error.

## Regex Block - Compiled Regular Expressions

    The `re{}` block provides regular expressions without string escaping noise.
    Patterns are compiled at build time when possible.

    **Type:** `std.regex.Pattern`

    **Features:**
    - Named capture groups
    - Compile-time validation
    - Flags (i, m, s, x)

Basic pattern matching.

Character class patterns.

Named captures for structured extraction.

Case insensitive matching with `i` flag.

Multiline mode with `m` flag.

Invalid regex produces compile-time error.

## Markdown Block - Document Embedding

    The `md{}` block embeds Markdown content directly in source code.
    Supports embedded sub-blocks for math and diagrams.

    **Type:** `std.doc.Markdown`

Headers, paragraphs, lists.

Inline code spans.

Fenced code blocks.

Math blocks via `${m{...}}` interpolation.

Math blocks via fenced syntax.

## Graph Block - Diagram Embedding

    The `graph{}` block embeds diagrams using text-based DSLs like Mermaid or DOT.

    **Type:** `std.graph.Diagram { format: str, asset_ref: AssetRef }`

Mermaid flowchart syntax.

Graphviz DOT syntax.

Diagrams can be embedded in markdown docs.

## Image Block - Image Embedding

    The `img{}` block embeds existing images or generates new ones.

    **Type:** `std.media.Image { format: str, asset_ref: AssetRef }`

    **Note:** Image generation requires explicit opt-in via package config.

Load image from file path.

Explicit format specification.

## HTML Block - Raw HTML Content

    The `html{}` block embeds HTML content directly.

    **Type:** `std.doc.Html`

Basic HTML elements.

Simple expressions can be interpolated.

Math expressions render as MathML.

## Nested Blocks and Interpolation

    Blocks can be nested via interpolation `${...}`. The interpolated
    expression must implement a render interface for the host block.

Math block renders inside markdown.

Graph block renders inside markdown.

Multiple block types in one document.

## User-Defined Block Kinds

    Users can define custom block handlers via the `__block__` dunder interface.

Custom block with __block__ dunder.

## Compile-Time and Runtime Errors

    Block parse errors are compile-time. Execution errors (sh{}) are runtime.

Invalid math syntax is caught at compile time.

Invalid regex is caught at compile time.

Invalid SQL is caught at compile time.

Shell execution errors are returned, not thrown.
