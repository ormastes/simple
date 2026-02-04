; Tree-sitter Injection Queries for Simple Language
; Defines embedded language regions for syntax highlighting

; ============================================================================
; Custom Blocks - Embedded DSL languages
; ============================================================================

; SQL blocks: sql{SELECT * FROM users}
((custom_block_expr) @injection.content
  (#match? @injection.content "^sql\\{")
  (#set! injection.language "sql")
  (#set! injection.include-children))

; Shell blocks: sh{ls -la | grep .spl}
((custom_block_expr) @injection.content
  (#match? @injection.content "^sh\\{")
  (#set! injection.language "bash")
  (#set! injection.include-children))

; Regex blocks: re{[A-Z][a-z]+}
((custom_block_expr) @injection.content
  (#match? @injection.content "^re\\{")
  (#set! injection.language "regex")
  (#set! injection.include-children))

; HTML blocks: html{<div>content</div>}
((custom_block_expr) @injection.content
  (#match? @injection.content "^html\\{")
  (#set! injection.language "html")
  (#set! injection.include-children))

; Markdown blocks: md{# Heading}
((custom_block_expr) @injection.content
  (#match? @injection.content "^md\\{")
  (#set! injection.language "markdown")
  (#set! injection.include-children))

; JSON blocks: json{{"key": "value"}}
((custom_block_expr) @injection.content
  (#match? @injection.content "^json\\{")
  (#set! injection.language "json")
  (#set! injection.include-children))

; CSS blocks: css{body { margin: 0; }}
((custom_block_expr) @injection.content
  (#match? @injection.content "^css\\{")
  (#set! injection.language "css")
  (#set! injection.include-children))

; JavaScript blocks: js{console.log("hello")}
((custom_block_expr) @injection.content
  (#match? @injection.content "^js\\{")
  (#set! injection.language "javascript")
  (#set! injection.include-children))

; Python blocks: py{print("hello")}
((custom_block_expr) @injection.content
  (#match? @injection.content "^py\\{")
  (#set! injection.language "python")
  (#set! injection.include-children))

; GraphQL blocks: graph{query { user { name } }}
((custom_block_expr) @injection.content
  (#match? @injection.content "^graph\\{")
  (#set! injection.language "graphql")
  (#set! injection.include-children))

; YAML blocks: yaml{key: value}
((custom_block_expr) @injection.content
  (#match? @injection.content "^yaml\\{")
  (#set! injection.language "yaml")
  (#set! injection.include-children))

; TOML blocks: toml{[section]}
((custom_block_expr) @injection.content
  (#match? @injection.content "^toml\\{")
  (#set! injection.language "toml")
  (#set! injection.include-children))

; Lean blocks: lean{theorem name : prop := proof}
((custom_block_expr) @injection.content
  (#match? @injection.content "^lean\\{")
  (#set! injection.language "lean")
  (#set! injection.include-children))

; ============================================================================
; F-Strings - Embedded expressions in strings
; ============================================================================

; F-string interpolation: "Hello {name}!"
(fstring_interpolation
  (expression) @injection.content
  (#set! injection.language "simple")
  (#set! injection.include-children))

; ============================================================================
; Doc Comments - Embedded markdown in documentation
; ============================================================================

; Doc comments with markdown syntax
((doc_comment) @injection.content
  (#set! injection.language "markdown")
  (#set! injection.include-children))

; ============================================================================
; Calc Blocks - Embedded mathematical reasoning
; ============================================================================

; Calc step expressions (could be highlighted as math)
(calc_step
  left: (expression) @injection.content
  (#set! injection.language "simple"))

(calc_step
  right: (expression) @injection.content
  (#set! injection.language "simple"))

; ============================================================================
; Pointcut Expressions - Embedded AOP query language
; ============================================================================

; Pointcut expressions have their own mini-language
((pointcut_expr) @injection.content
  (#set! injection.language "pointcut")
  (#set! injection.include-children))

; ============================================================================
; Contract Expressions - Verification logic
; ============================================================================

; Requires/ensures predicates (could use SMT syntax if supported)
(requires_stmt
  condition: (expression) @injection.content
  (#set! injection.language "simple"))

(ensures_stmt
  condition: (expression) @injection.content
  (#set! injection.language "simple"))

(out_stmt
  body: (_) @injection.content
  (#set! injection.language "simple")
  (#set! injection.include-children))

(out_err_stmt
  body: (_) @injection.content
  (#set! injection.language "simple")
  (#set! injection.include-children))

; ============================================================================
; BDD Step Patterns - Could support Gherkin syntax
; ============================================================================

; BDD step patterns as strings
(given_step
  pattern: (string_literal) @injection.content
  (#set! injection.language "gherkin"))

(when_step
  pattern: (string_literal) @injection.content
  (#set! injection.language "gherkin"))

(then_step
  pattern: (string_literal) @injection.content
  (#set! injection.language "gherkin"))

(and_then_step
  pattern: (string_literal) @injection.content
  (#set! injection.language "gherkin"))

; ============================================================================
; Macro Blocks - Embedded template syntax
; ============================================================================

; Macro blocks: m{div.class="container"}
((custom_block_expr) @injection.content
  (#match? @injection.content "^m\\{")
  (#set! injection.language "pug")
  (#set! injection.include-children))

; ============================================================================
; Raw Strings - No processing
; ============================================================================

; Raw strings should not be processed
(raw_string_literal) @injection.content
  (#set! injection.language "text")

; ============================================================================
; Code Examples in Comments - Embedded Simple code
; ============================================================================

; Code blocks in doc comments (markdown fenced code blocks)
((doc_comment) @injection.content
  (#match? @injection.content "```simple")
  (#set! injection.language "simple")
  (#set! injection.include-children))

((doc_comment) @injection.content
  (#match? @injection.content "```spl")
  (#set! injection.language "simple")
  (#set! injection.include-children))
