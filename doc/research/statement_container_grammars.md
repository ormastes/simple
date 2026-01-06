# Statement Container Grammar Comparison

**Status:** Research
**Created:** 2026-01-05
**Updated:** 2026-01-06
**Purpose:** Comparative analysis of statement container syntax across programming languages
**Topics:** syntax, grammar, control-flow

This document compares the grammar specifications for statement containers (loops, conditionals, pattern matching) across multiple programming languages to inform Simple's syntax design.

**See Also:** [Code Shortening Grammar Analysis](code_shortening_grammar_analysis.md) - Comprehensive analysis of high-leverage syntax features beyond control flow (comprehensions, pipelines, error propagation, optional chaining, etc.)

## Contents

1. [Grammar Notation Key](#grammar-notation-key)
2. [Language Comparisons](#language-comparisons)
   - [Python (PEG)](#python-peg)
   - [Go (EBNF)](#go-ebnf)
   - [Rust (EBNF)](#rust-ebnf)
   - [Ruby (Yacc)](#ruby-yacc)
   - [Kotlin (EBNF)](#kotlin-ebnf)
   - [Swift (ANTLR)](#swift-antlr)
   - [Zig (PEG)](#zig-peg)
3. [Pattern Analysis](#pattern-analysis)
4. [Simple Language Comparison](#simple-language-comparison)
5. [Design Insights](#design-insights)

---

## Grammar Notation Key

| Notation | EBNF | PEG | Yacc/ANTLR | Meaning |
|----------|------|-----|------------|---------|
| Optional | `[...]` | `?` | `?` | 0 or 1 occurrence |
| Repetition (0+) | `{...}` | `*` | `*` | 0 or more |
| Repetition (1+) | - | `+` | `+` | 1 or more |
| Alternation | `\|` | `/` | `\|` | Choice |
| Grouping | `(...)` | `(...)` | `(...)` | Group elements |
| Sequence | space | space | space | Concatenation |
| Terminal | `"..."` | `'...'` | `'...'` | Literal text |
| Non-terminal | word | Word | word | Rule reference |

---

## Language Comparisons

### Python (PEG)

**Grammar Type:** PEG (Parsing Expression Grammar)
**Source:** [Python 3.14.2 Grammar](https://docs.python.org/3/reference/grammar.html)

#### For Statement
```python
for_stmt:
    | 'for' star_targets 'in' ~ star_expressions ':' [TYPE_COMMENT] block [else_block]
    | 'async' 'for' star_targets 'in' ~ star_expressions ':' [TYPE_COMMENT] block [else_block]
```

#### If Statement
```python
if_stmt:
    | 'if' named_expression ':' block elif_stmt
    | 'if' named_expression ':' block [else_block]

elif_stmt:
    | 'elif' named_expression ':' block elif_stmt
    | 'elif' named_expression ':' block [else_block]
```

#### While Statement
```python
while_stmt:
    | 'while' named_expression ':' block [else_block]
```

#### Match Statement
```python
match_stmt:
    | "match" subject_expr ':' NEWLINE INDENT case_block+ DEDENT

case_block:
    | "case" patterns guard? ':' block

guard: 'if' named_expression
```

#### Try Statement
```python
try_stmt:
    | 'try' ':' block finally_block
    | 'try' ':' block except_block+ [else_block] [finally_block]
    | 'try' ':' block except_star_block+ [else_block] [finally_block]
```

**Key Features:**
- **Indentation-based blocks** with `INDENT`/`DEDENT` tokens
- **Colon separator** between condition and block
- **Optional else clauses** on loops
- **Pattern matching** with guards
- **Async variants** for concurrent code

---

### Go (EBNF)

**Grammar Type:** EBNF (Extended Backus-Naur Form)
**Source:** [Go Language Specification](https://go.dev/ref/spec)

#### For Statement
```ebnf
ForStmt = "for" [ InitStmt ";" Condition ";" PostStmt ] Block
        | "for" Condition Block
        | "for" Block .

InitStmt = SimpleStmt .
PostStmt = SimpleStmt .
```

#### If Statement
```ebnf
IfStmt = "if" [ InitStmt ";" ] Expression Block [ "else" ( IfStmt | Block ) ] .
```

#### Switch Statement
```ebnf
SwitchStmt = ExprSwitchStmt | TypeSwitchStmt .

ExprSwitchStmt = "switch" [ InitStmt ";" ] [ Expression ] "{" { ExprCaseClause } "}" .
ExprCaseClause = ExprSwitchCase ":" StatementList .
ExprSwitchCase = "case" ExpressionList | "default" .

TypeSwitchStmt = "switch" [ InitStmt ";" ] TypeSwitchGuard "{" { TypeCaseClause } "}" .
```

**Key Features:**
- **Brace-delimited blocks** `{ }`
- **Optional init statement** before condition (C-style)
- **Three-part for loop** (init; condition; post)
- **Type switch** for interface dispatch
- **No parentheses** required around conditions

---

### Rust (EBNF)

**Grammar Type:** EBNF
**Source:** [Rust Grammar v1.25](https://web.mit.edu/rust-lang_v1.25/arch/amd64_ubuntu1404/share/doc/rust/html/grammar.html)

#### For Loop
```ebnf
for_expr : [ lifetime ':' ] ? "for" pat "in" no_struct_literal_expr '{' block '}' ;
```

#### If Expression
```ebnf
if_expr : "if" no_struct_literal_expr '{' block '}'
          else_tail ? ;

else_tail : "else" [ if_expr | if_let_expr
                   | '{' block '}' ] ;
```

#### While Loop
```ebnf
while_expr : [ lifetime ':' ] ? "while" no_struct_literal_expr '{' block '}' ;
```

#### Match Expression
```ebnf
match_expr : "match" no_struct_literal_expr '{' match_arm * '}' ;

match_arm : attribute * match_pat "=>" [ expr "," | '{' block '}' ] ;

match_pat : pat [ '|' pat ] * [ "if" expr ] ? ;
```

**Key Features:**
- **Expressions, not statements** (return values)
- **Pattern matching** in for/if/match
- **Optional lifetime labels** for labeled breaks
- **Guard clauses** in match arms
- **No parentheses** around conditions

---

### Ruby (Yacc)

**Grammar Type:** Yacc/Bison
**Source:** [Ruby parse.y](https://github.com/ruby/ruby/blob/2b54c135ff3ae2fb362a5efaa542ec9236116add/parse.y)

#### For Loop
```yacc
for_var: tIDENTIFIER | mlhs
for_body: do_body | compstmt
```

#### If Statement
```yacc
if_tail: keyword_else compstmt
       | keyword_elsif expr_value then compstmt if_tail
```

#### While Loop
```yacc
stmt: stmt modifier_while expr_value
```

#### Case/When Statement
```yacc
case_body: keyword_when case_args then compstmt cases
cases: opt_else
     | case_body
```

**Key Features:**
- **Statement modifiers** (postfix conditionals/loops)
- **Flexible syntax** (do/end or braces)
- **Expression-oriented** (everything returns a value)
- **Optional parentheses** and keywords

---

### Kotlin (EBNF)

**Grammar Type:** EBNF (ISO/IEC 14977-like)
**Source:** [Kotlin Language Specification](https://kotlinlang.org/spec/syntax-and-grammar.html)

#### For Statement
```ebnf
forStatement:
  'for' {NL} '(' {annotation}
  (variableDeclaration | multiVariableDeclaration)
  'in' expression ')'
  {NL} [controlStructureBody]
```

#### If Expression
```ebnf
ifExpression:
  'if' {NL} '(' expression ')' {NL}
  controlStructureBody
  [({NL} 'else' {NL} controlStructureBody)]
```

#### While Statement
```ebnf
whileStatement:
  'while' {NL} '(' expression ')'
  {NL} (controlStructureBody | ';')
```

#### When Expression
```ebnf
whenExpression:
  'when' {NL} ['(' expression ')'] {NL} '{'
  {NL} {whenEntry {NL}}
  {NL} '}'

whenEntry:
  (whenCondition {{NL} ',' {NL} whenCondition} [({NL} ',')]) {NL} '->' {NL} controlStructureBody
  | 'else' {NL} '->' {NL} controlStructureBody
```

**Key Features:**
- **Expression-oriented** (if/when return values)
- **Flexible newlines** `{NL}` around most tokens
- **Pattern matching** with when
- **Destructuring** in for loops
- **Arrow syntax** `->` for when branches

---

### Swift (ANTLR)

**Grammar Type:** ANTLR
**Source:** [ANTLR Swift3 Grammar](https://github.com/antlr/grammars-v4/blob/master/swift/swift3/Swift3.g4)

#### For-In Statement
```antlr
for_in_statement
    : 'for' 'case'? pattern 'in' expression where_clause? code_block
    ;
```

#### If Statement
```antlr
if_statement
    : 'if' condition_list code_block else_clause?
    ;

else_clause
    : 'else' code_block
    | 'else' if_statement
    ;
```

#### While Statement
```antlr
while_statement
    : 'while' condition_list code_block
    ;

condition_list
    : condition (',' condition)*
    ;
```

#### Switch Statement
```antlr
switch_statement
    : 'switch' expression '{' switch_cases? '}'
    ;

switch_case
    : case_label statements
    | default_label statements
    ;
```

**Key Features:**
- **Pattern matching** in for loops (optional `case`)
- **Where clauses** for filtering
- **Multiple conditions** separated by commas
- **Brace-delimited blocks**

---

### Zig (PEG)

**Grammar Type:** PEG (Parsing Expression Grammar)
**Source:** [Zig Grammar Spec](https://github.com/ziglang/zig-spec/blob/master/grammar/grammar.peg)

#### If Statement
```peg
IfStatement <- IfPrefix BlockExpr ( KEYWORD_else Payload? Statement )?
            / IfPrefix AssignExpr ( SEMICOLON / KEYWORD_else Payload? Statement )
```

#### For Statement
```peg
ForStatement <- ForPrefix BlockExpr ( KEYWORD_else Statement )?
             / ForPrefix AssignExpr ( SEMICOLON / KEYWORD_else Statement )
```

#### While Statement
```peg
WhileStatement <- WhilePrefix BlockExpr ( KEYWORD_else Payload? Statement )?
               / WhilePrefix AssignExpr ( SEMICOLON / KEYWORD_else Statement )
```

#### Switch Expression
```peg
SwitchExpr <- KEYWORD_switch LPAREN Expr RPAREN LBRACE SwitchProngList RBRACE
```

**Key Features:**
- **Dual forms:** block expression or assignment expression
- **Optional else clauses** on loops
- **Payload capture** for error handling
- **Compact grammar** (580 lines for entire language)

---

## Pattern Analysis

### Block Delimiters

| Language | Block Style | Example |
|----------|-------------|---------|
| Python | Indentation + `:` | `if x:\n    body` |
| Go | Braces `{ }` | `if x { body }` |
| Rust | Braces `{ }` | `if x { body }` |
| Ruby | `do...end` or `{ }` | `if x then body end` |
| Kotlin | Braces or single expr | `if (x) { body }` |
| Swift | Braces `{ }` | `if x { body }` |
| Zig | Braces `{ }` | `if (x) { body }` |

**Insight:** Only Python and Simple use indentation-based blocks. All others use braces.

### Condition Delimiters

| Language | Parentheses Required | Example |
|----------|---------------------|---------|
| Python | No | `if condition:` |
| Go | No | `if condition {` |
| Rust | No | `if condition {` |
| Ruby | No | `if condition then` |
| Kotlin | Yes | `if (condition)` |
| Swift | No (deprecated) | `if condition {` |
| Zig | Yes | `if (condition)` |

**Insight:** Modern trend is away from required parentheses around conditions.

### Pattern Matching Syntax

| Language | Keyword | Branch Separator | Guard Syntax |
|----------|---------|------------------|--------------|
| Python | `match/case` | `:` | `if guard` |
| Go | `switch/case` | `:` | N/A (use if) |
| Rust | `match` | `=>` | `if guard` |
| Ruby | `case/when` | (implicit) | N/A |
| Kotlin | `when` | `->` | N/A (use if in condition) |
| Swift | `switch/case` | `:` | `where clause` |
| Zig | `switch` | `=>` | N/A |

**Insight:** Arrow syntax (`=>`, `->`) is common for pattern matching. Guards vary widely.

### For Loop Styles

| Language | Style | Syntax |
|----------|-------|--------|
| Python | Iterator | `for x in iterable:` |
| Go | C-style/Iterator | `for init; cond; post { }` or `for x := range y { }` |
| Rust | Iterator only | `for x in iterable { }` |
| Ruby | Iterator/Blocks | `for x in arr do` or `arr.each { \|x\| }` |
| Kotlin | Iterator only | `for (x in collection)` |
| Swift | Iterator only | `for x in collection { }` |
| Zig | Iterator | `for (slice) \|item\| { }` |

**Insight:** Modern languages prefer iterator-style over C-style (init; cond; post).

### Expression vs Statement

| Language | Control Flow as Expression? | Example |
|----------|----------------------------|---------|
| Python | No (statement-based) | `x = (1 if cond else 0)` (special syntax) |
| Go | No | Cannot assign if result |
| Rust | **Yes** | `let x = if cond { 1 } else { 0 };` |
| Ruby | **Yes** | `x = if cond then 1 else 0 end` |
| Kotlin | **Yes** | `val x = if (cond) 1 else 0` |
| Swift | **Partial** | `if` is statement, but ternary exists |
| Zig | **Yes** | `const x = if (cond) 1 else 0;` |

**Insight:** Expression-oriented control flow is increasingly popular (Rust, Kotlin, Zig).

---

## Simple Language Comparison

### Current Simple Syntax

Based on `doc/spec/parser/lexer_parser_grammar.md`:

#### For Statement
```
for_stmt:
    "for" pattern "in" expression ":" block
```

#### If Statement
```
if_stmt:
    "if" expression ":" block
    ("elif" expression ":" block)*
    ("else" ":" block)?
```

#### While Statement
```
while_stmt:
    "while" expression ":" block
    ("else" ":" block)?
```

#### Match Statement
```
match_stmt:
    "match" expression ":"
        INDENT
        ("case" pattern ("if" expression)? ":" block)+
        ("default" ":" block)?
        DEDENT
```

### Simple's Design Choices

| Feature | Choice | Rationale |
|---------|--------|-----------|
| Block delimiter | **Indentation + `:`** | Python-like readability |
| Condition parens | **No** | Cleaner syntax (Rust/Go-style) |
| Expression-oriented | **Yes** (planned) | Rust/Kotlin-style flexibility |
| Pattern matching | **`match/case`** | Rust-inspired with Python syntax |
| Guard clauses | **`if guard`** | Python/Rust-style |
| For loop | **Iterator-only** | Modern style |
| Optional else on loops | **Yes** | Python-style convenience |

---

## Design Insights

### 1. Indentation vs Braces

**Languages with indentation:** Python, Simple
**Languages with braces:** Go, Rust, Kotlin, Swift, Zig

**Tradeoffs:**
- **Indentation:** Forces consistent style, cleaner appearance, requires INDENT/DEDENT tokens
- **Braces:** More flexible formatting, easier to parse, familiar to C-family developers

**Simple's choice:** Indentation (like Python) prioritizes readability and reduces syntactic noise.

### 2. Colon Separator

**Languages using `:`:** Python, Simple, Go (in switch cases), Swift (in switch cases)

**Purpose:**
- Visual separator between condition and body
- Signals start of indented block
- Improves readability when parentheses are omitted

**Simple's choice:** Colon separator balances Python's readability with modern no-parens style.

### 3. Expression-Oriented Design

**Advantages:**
- Reduces need for ternary operator
- Enables functional programming patterns
- Simplifies value assignment from control flow
- Consistent with Rust/Kotlin/Zig trend

**Simple's opportunity:** Support expressions while maintaining statement-level clarity with indentation.

### 4. Pattern Matching Evolution

**Trends:**
- **Arrow syntax** (`=>`, `->`) increasingly common
- **Guard clauses** essential for complex patterns
- **Exhaustiveness checking** (Rust/Swift-style)
- **Pattern destructuring** in match and for loops

**Simple's approach:** Rust-style semantics with Python-style syntax (`:` separator, indentation).

### 5. Minimal Syntax

**Zig's achievement:** 580-line PEG grammar for entire language

**Keys to brevity:**
- Consistent rules across constructs
- Minimal special cases
- Regular composition of features

**Simple's goal:** Balance brevity with expressiveness (Python's readability + Rust's power).

### 6. Newline Flexibility

**Kotlin's `{NL}` approach:** Allow newlines almost anywhere for formatting freedom

**Tradeoff:**
- More flexible formatting
- More complex grammar/parser
- Potential ambiguity

**Simple's approach:** Strict indentation rules simplify parsing and enforce style consistency.

### 7. Unified Statement Container Pattern

**Common structure across languages:**
```
KEYWORD [init] condition SEPARATOR body [else-clause]
```

**Variations:**
- **KEYWORD:** `if`, `while`, `for`, `match`, `switch`
- **init:** Optional initialization (Go-style)
- **condition:** Expression or pattern
- **SEPARATOR:** `:`, `{`, `then`, `do`
- **body:** Block or single statement
- **else-clause:** Optional alternative branch

**Simple's implementation:** Consistent `KEYWORD condition : block` pattern with optional else.

---

## Recommendations for Simple

### Current Strengths

1. ✅ **Clean syntax** with indentation and colons
2. ✅ **Modern pattern matching** with guards
3. ✅ **No parentheses** around conditions
4. ✅ **Iterator-style for loops**
5. ✅ **Consistent block syntax** across all constructs

### Potential Enhancements

1. **Expression-oriented control flow**
   - Allow `let x = if cond: value1 else: value2`
   - Requires all branches to return compatible types
   - Improves functional programming ergonomics

2. **Destructuring in for loops**
   - Current: `for x in items:`
   - Enhanced: `for (key, value) in dict:` or `for Point(x, y) in points:`
   - Aligns with Kotlin/Swift patterns

3. **Optional loop labels**
   - Rust-style: `'outer: while cond:`
   - Enables labeled break/continue
   - Useful for nested loops

4. **When expression** (alternative to match)
   - Kotlin-style: `when condition:` with `-> value` branches
   - More concise for simple dispatching
   - Could coexist with pattern-based match

5. **Compact else syntax**
   - Current: `else:` + newline + indent
   - Option: `else: single_expr` for inline else
   - Reduces vertical space for simple cases

---

## References

### Primary Sources

- [Python 3.14.2 Grammar Specification](https://docs.python.org/3/reference/grammar.html)
- [Go Language Specification](https://go.dev/ref/spec)
- [Rust Grammar v1.25](https://web.mit.edu/rust-lang_v1.25/arch/amd64_ubuntu1404/share/doc/rust/html/grammar.html)
- [Ruby parse.y](https://github.com/ruby/ruby/blob/2b54c135ff3ae2fb362a5efaa542ec9236116add/parse.y)
- [Kotlin Language Specification](https://kotlinlang.org/spec/syntax-and-grammar.html)
- [Swift ANTLR Grammar](https://github.com/antlr/grammars-v4/blob/master/swift/swift3/Swift3.g4)
- [Zig Grammar Specification](https://github.com/ziglang/zig-spec/blob/master/grammar/grammar.peg)

### Related Documentation

- [Simple Grammar Specification](../spec/parser/lexer_parser_grammar.md)
- [Simple Syntax Specification](../spec/syntax.md)
- [Simple Pattern Matching Specification](../spec/functions.md#pattern-matching)

---

## Conclusion

Simple's current syntax aligns well with modern language design trends:

- **Indentation-based blocks** (like Python) for readability
- **No parentheses** around conditions (like Rust/Go)
- **Pattern matching** with guards (like Rust)
- **Iterator-style for loops** (modern standard)

The main opportunity for evolution is toward **expression-oriented control flow** (following Rust/Kotlin/Zig), which would enhance functional programming capabilities while maintaining Simple's clean, readable syntax.

The comparative analysis shows that Simple's grammar is **concise yet expressive**, comparable to Zig's minimalism while retaining Python's approachability.

---

## Next Steps

For a comprehensive analysis of **code-shortening grammar features** beyond control flow (error propagation, optional chaining, pipelines, etc.), see:

**[Code Shortening Grammar Analysis](code_shortening_grammar_analysis.md)**

This companion document evaluates 18 high-leverage syntax features across 7 categories:
- Collection construction (comprehensions, spread, ranges, slicing)
- Transformation pipelines (method chains, pipeline operator, placeholders)
- Binding & destructuring
- Null/optional safety (optional chaining, nullish coalescing)
- Error propagation (Rust-style `?` operator)
- Function/lambda brevity
- String & literal ergonomics

Each feature includes:
- Current status in Simple
- Detailed syntax proposals
- Implementation guidance
- Priority recommendations
