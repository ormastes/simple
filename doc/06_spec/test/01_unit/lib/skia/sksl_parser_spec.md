# SkSL Parser Specification

> Tests for `parse_sksl` — the minimal SkSL AST builder that consumes a `Token` stream produced by `tokenize_sksl` and emits a small AST. The subset is: uniform declarations, function definitions, return / variable-decl / assign / expression statements, and a flat expression grammar with left-chained binary ops.

<!-- sdn-diagram:id=sksl_parser_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sksl_parser_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sksl_parser_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sksl_parser_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SkSL Parser Specification

Tests for `parse_sksl` — the minimal SkSL AST builder that consumes a `Token` stream produced by `tokenize_sksl` and emits a small AST. The subset is: uniform declarations, function definitions, return / variable-decl / assign / expression statements, and a flat expression grammar with left-chained binary ops.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-SKSL-002 |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/skia/sksl_parser_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for `parse_sksl` — the minimal SkSL AST builder that consumes a
`Token` stream produced by `tokenize_sksl` and emits a small AST. The
subset is: uniform declarations, function definitions, return /
variable-decl / assign / expression statements, and a flat expression
grammar with left-chained binary ops.

Tokens are constructed manually here so the parser is exercised in
isolation (without depending on tokenize_sksl semantics bleeding into
parser tests).

## Scenarios

### sksl_parser

#### parse_sksl: empty token list (just Eof) returns empty ast, no errors

1. toks push
   - Expected: r.ast.len() equals `0`
   - Expected: r.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var toks: [Token] = []
toks.push(_eof())
val r = parse_sksl(toks)
expect(r.ast.len()).to_equal(0)
expect(r.errors.len()).to_equal(0)
```

</details>

#### parse_sksl: uniform declaration \

1. toks push
2. toks push
3. toks push
4. toks push
5. toks push
   - Expected: r.errors.len() equals `0`
   - Expected: r.ast.len() equals `1`
   - Expected: r.ast[0].kind == AstNodeKind.Uniform is true
   - Expected: r.ast[0].text equals `u_time`
   - Expected: r.ast[0].type_name equals `float`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var toks: [Token] = []
toks.push(_tok(TokenKind.Keyword, "uniform"))
toks.push(_tok(TokenKind.Keyword, "float"))
toks.push(_tok(TokenKind.Identifier, "u_time"))
toks.push(_tok(TokenKind.Punctuation, ";"))
toks.push(_eof())
val r = parse_sksl(toks)
expect(r.errors.len()).to_equal(0)
expect(r.ast.len()).to_equal(1)
expect(r.ast[0].kind == AstNodeKind.Uniform).to_equal(true)
expect(r.ast[0].text).to_equal("u_time")
expect(r.ast[0].type_name).to_equal("float")
```

</details>

#### parse_sksl: function definition \

1. toks push
2. toks push
3. toks push
4. toks push
5. toks push
6. toks push
7. toks push
   - Expected: r.errors.len() equals `0`
   - Expected: r.ast.len() equals `1`
   - Expected: r.ast[0].kind == AstNodeKind.Function is true
   - Expected: r.ast[0].text equals `main`
   - Expected: r.ast[0].type_name equals `void`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var toks: [Token] = []
toks.push(_tok(TokenKind.Keyword, "void"))
toks.push(_tok(TokenKind.Identifier, "main"))
toks.push(_tok(TokenKind.Punctuation, "("))
toks.push(_tok(TokenKind.Punctuation, ")"))
toks.push(_tok(TokenKind.Punctuation, "{"))
toks.push(_tok(TokenKind.Punctuation, "}"))
toks.push(_eof())
val r = parse_sksl(toks)
expect(r.errors.len()).to_equal(0)
expect(r.ast.len()).to_equal(1)
expect(r.ast[0].kind == AstNodeKind.Function).to_equal(true)
expect(r.ast[0].text).to_equal("main")
expect(r.ast[0].type_name).to_equal("void")
```

</details>

#### parse_sksl: return statement inside function body produces a ReturnStmt child

1. toks push
2. toks push
3. toks push
4. toks push
5. toks push
6. toks push
7. toks push
8. toks push
9. toks push
10. toks push
   - Expected: r.errors.len() equals `0`
   - Expected: r.ast.len() equals `1`
   - Expected: fn_node.kind == AstNodeKind.Function is true
   - Expected: fn_node.children[0].kind == AstNodeKind.ReturnStmt is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# void main() { return 0 ; }
var toks: [Token] = []
toks.push(_tok(TokenKind.Keyword, "void"))
toks.push(_tok(TokenKind.Identifier, "main"))
toks.push(_tok(TokenKind.Punctuation, "("))
toks.push(_tok(TokenKind.Punctuation, ")"))
toks.push(_tok(TokenKind.Punctuation, "{"))
toks.push(_tok(TokenKind.Keyword, "return"))
toks.push(_tok(TokenKind.IntLiteral, "0"))
toks.push(_tok(TokenKind.Punctuation, ";"))
toks.push(_tok(TokenKind.Punctuation, "}"))
toks.push(_eof())
val r = parse_sksl(toks)
expect(r.errors.len()).to_equal(0)
expect(r.ast.len()).to_equal(1)
val fn_node = r.ast[0]
expect(fn_node.kind == AstNodeKind.Function).to_equal(true)
expect(fn_node.children.len()).to_be_greater_than(0)
expect(fn_node.children[0].kind == AstNodeKind.ReturnStmt).to_equal(true)
```

</details>

#### parse_sksl: int literal is parsed into IntLit

1. toks push
2. toks push
3. toks push
4. toks push
5. toks push
6. toks push
7. toks push
8. toks push
9. toks push
10. toks push
11. toks push
12. toks push
   - Expected: r.ast.len() equals `1`
   - Expected: fn_node.children.len() equals `1`
   - Expected: decl.kind == AstNodeKind.VarDecl is true
   - Expected: decl.children.len() equals `1`
   - Expected: lit.kind == AstNodeKind.IntLit is true
   - Expected: lit.int_value equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# int x = 42 ;  (top-level to exercise a decl path; the int literal
# expression lives on the VarDecl's child expression.)
# Build as a function body: void f() { int x = 42 ; }
var toks: [Token] = []
toks.push(_tok(TokenKind.Keyword, "void"))
toks.push(_tok(TokenKind.Identifier, "f"))
toks.push(_tok(TokenKind.Punctuation, "("))
toks.push(_tok(TokenKind.Punctuation, ")"))
toks.push(_tok(TokenKind.Punctuation, "{"))
toks.push(_tok(TokenKind.Keyword, "int"))
toks.push(_tok(TokenKind.Identifier, "x"))
toks.push(_tok(TokenKind.Operator, "="))
toks.push(_tok(TokenKind.IntLiteral, "42"))
toks.push(_tok(TokenKind.Punctuation, ";"))
toks.push(_tok(TokenKind.Punctuation, "}"))
toks.push(_eof())
val r = parse_sksl(toks)
expect(r.ast.len()).to_equal(1)
val fn_node = r.ast[0]
expect(fn_node.children.len()).to_equal(1)
val decl = fn_node.children[0]
expect(decl.kind == AstNodeKind.VarDecl).to_equal(true)
expect(decl.children.len()).to_equal(1)
val lit = decl.children[0]
expect(lit.kind == AstNodeKind.IntLit).to_equal(true)
expect(lit.int_value).to_equal(42)
```

</details>

#### parse_sksl: identifier expression is parsed into Identifier

1. toks push
2. toks push
3. toks push
4. toks push
5. toks push
6. toks push
7. toks push
8. toks push
9. toks push
   - Expected: r.ast.len() equals `1`
   - Expected: fn_node.children.len() equals `1`
   - Expected: stmt.kind == AstNodeKind.ExpressionStmt is true
   - Expected: stmt.children.len() equals `1`
   - Expected: ident.kind == AstNodeKind.Identifier is true
   - Expected: ident.text equals `x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# void f() { x ; }
var toks: [Token] = []
toks.push(_tok(TokenKind.Keyword, "void"))
toks.push(_tok(TokenKind.Identifier, "f"))
toks.push(_tok(TokenKind.Punctuation, "("))
toks.push(_tok(TokenKind.Punctuation, ")"))
toks.push(_tok(TokenKind.Punctuation, "{"))
toks.push(_tok(TokenKind.Identifier, "x"))
toks.push(_tok(TokenKind.Punctuation, ";"))
toks.push(_tok(TokenKind.Punctuation, "}"))
toks.push(_eof())
val r = parse_sksl(toks)
expect(r.ast.len()).to_equal(1)
val fn_node = r.ast[0]
expect(fn_node.children.len()).to_equal(1)
val stmt = fn_node.children[0]
expect(stmt.kind == AstNodeKind.ExpressionStmt).to_equal(true)
expect(stmt.children.len()).to_equal(1)
val ident = stmt.children[0]
expect(ident.kind == AstNodeKind.Identifier).to_equal(true)
expect(ident.text).to_equal("x")
```

</details>

#### parse_sksl: malformed input records a non-empty errors list

1. toks push
2. toks push
3. toks push


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# garbage top-level: `? ;` — a bare operator+semicolon doesn't
# match any top-level construct and should be flagged.
var toks: [Token] = []
toks.push(_tok(TokenKind.Operator, "?"))
toks.push(_tok(TokenKind.Punctuation, ";"))
toks.push(_eof())
val r = parse_sksl(toks)
expect(r.errors.len()).to_be_greater_than(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
