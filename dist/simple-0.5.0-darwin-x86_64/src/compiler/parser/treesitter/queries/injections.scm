;; injections.scm - Language Injections
;; Tree-sitter query file for embedded language syntax highlighting
;; Enables: SQL in sql{}, HTML in html{}, etc.

;; ============================================================================
;; Custom Embedded Language Blocks
;; ============================================================================

;; SQL Block - sql{...}
((sql_block
  (block_content) @injection.content)
 (#set! injection.language "sql"))

;; Shell/Bash Block - sh{...}
((sh_block
  (block_content) @injection.content)
 (#set! injection.language "bash"))

;; Regex Block - re{...}
((re_block
  (block_content) @injection.content)
 (#set! injection.language "regex"))

;; HTML Block - html{...}
((html_block
  (block_content) @injection.content)
 (#set! injection.language "html"))

;; Markdown Block - md{...}
((md_block
  (block_content) @injection.content)
 (#set! injection.language "markdown"))

;; JSON Block - json{...}
((json_block
  (block_content) @injection.content)
 (#set! injection.language "json"))

;; CSS Block - css{...}
((css_block
  (block_content) @injection.content)
 (#set! injection.language "css"))

;; JavaScript Block - js{...}
((js_block
  (block_content) @injection.content)
 (#set! injection.language "javascript"))

;; Python Block - py{...}
((py_block
  (block_content) @injection.content)
 (#set! injection.language "python"))

;; GraphQL Block - graph{...}
((graph_block
  (block_content) @injection.content)
 (#set! injection.language "graphql"))

;; YAML Block - yaml{...}
((yaml_block
  (block_content) @injection.content)
 (#set! injection.language "yaml"))

;; TOML Block - toml{...}
((toml_block
  (block_content) @injection.content)
 (#set! injection.language "toml"))

;; Lean Block - lean{...}
((lean_block
  (block_content) @injection.content)
 (#set! injection.language "lean"))

;; Math Block - m{...}
((math_block
  (block_content) @injection.content)
 (#set! injection.language "latex"))

;; ============================================================================
;; F-String Interpolation
;; ============================================================================

;; Expressions inside interpolated strings "hello {expr}"
((interpolated_string
  (interpolation
    (expression) @injection.content))
 (#set! injection.language "simple"))

;; ============================================================================
;; Doc Comments
;; ============================================================================

;; Doc comments contain Markdown
((doc_comment) @injection.content
 (#set! injection.language "markdown"))

;; Line doc comments (///)
((line_doc_comment) @injection.content
 (#set! injection.language "markdown"))

;; Block doc comments (/** ... */)
((block_doc_comment) @injection.content
 (#set! injection.language "markdown"))

;; ============================================================================
;; Code Examples in Doc Comments
;; ============================================================================

;; ```simple or ```spl code blocks in doc comments
((doc_comment
  (code_block
    (code_fence_info) @_lang
    (code_block_content) @injection.content))
 (#match? @_lang "(simple|spl)")
 (#set! injection.language "simple"))

;; ```rust code blocks
((doc_comment
  (code_block
    (code_fence_info) @_lang
    (code_block_content) @injection.content))
 (#match? @_lang "rust")
 (#set! injection.language "rust"))

;; ```python code blocks
((doc_comment
  (code_block
    (code_fence_info) @_lang
    (code_block_content) @injection.content))
 (#match? @_lang "(python|py)")
 (#set! injection.language "python"))

;; ```javascript code blocks
((doc_comment
  (code_block
    (code_fence_info) @_lang
    (code_block_content) @injection.content))
 (#match? @_lang "(javascript|js)")
 (#set! injection.language "javascript"))

;; ```sql code blocks
((doc_comment
  (code_block
    (code_fence_info) @_lang
    (code_block_content) @injection.content))
 (#match? @_lang "sql")
 (#set! injection.language "sql"))

;; ```bash code blocks
((doc_comment
  (code_block
    (code_fence_info) @_lang
    (code_block_content) @injection.content))
 (#match? @_lang "(bash|sh|shell)")
 (#set! injection.language "bash"))

;; ```json code blocks
((doc_comment
  (code_block
    (code_fence_info) @_lang
    (code_block_content) @injection.content))
 (#match? @_lang "json")
 (#set! injection.language "json"))

;; ```html code blocks
((doc_comment
  (code_block
    (code_fence_info) @_lang
    (code_block_content) @injection.content))
 (#match? @_lang "html")
 (#set! injection.language "html"))

;; ```css code blocks
((doc_comment
  (code_block
    (code_fence_info) @_lang
    (code_block_content) @injection.content))
 (#match? @_lang "css")
 (#set! injection.language "css"))

;; ============================================================================
;; Calc Blocks (Mathematical Proofs)
;; ============================================================================

;; Calc blocks contain Simple expressions with mathematical notation
((calc_block
  (calc_body) @injection.content)
 (#set! injection.language "simple"))

;; Individual calc steps
((calc_step
  (expression) @injection.content)
 (#set! injection.language "simple"))

;; ============================================================================
;; Pointcut Expressions (AOP)
;; ============================================================================

;; Pointcut query language - pc{...}
((pointcut_expression
  (pointcut_body) @injection.content)
 (#set! injection.language "pointcut"))

;; ============================================================================
;; BDD Step Patterns
;; ============================================================================

;; Gherkin-style step patterns
((given_step
  (step_pattern) @injection.content)
 (#set! injection.language "gherkin"))

((when_step
  (step_pattern) @injection.content)
 (#set! injection.language "gherkin"))

((then_step
  (step_pattern) @injection.content)
 (#set! injection.language "gherkin"))

((and_then_step
  (step_pattern) @injection.content)
 (#set! injection.language "gherkin"))

;; ============================================================================
;; Regex in Different Contexts
;; ============================================================================

;; Regex literals
((regex_literal) @injection.content
 (#set! injection.language "regex"))

;; Raw strings used as regex (common pattern)
((raw_string_literal) @injection.content
 (#match? @injection.content "^r\".*\\\\[dDwWsS]")
 (#set! injection.language "regex"))

;; ============================================================================
;; String Templates with Syntax
;; ============================================================================

;; SQL in string literals (heuristic: starts with SELECT/INSERT/UPDATE/DELETE)
((string_literal) @injection.content
 (#match? @injection.content "^\"\\s*(SELECT|INSERT|UPDATE|DELETE|CREATE|DROP|ALTER)")
 (#set! injection.language "sql"))

;; HTML in string literals (heuristic: starts with <html or <!DOCTYPE)
((string_literal) @injection.content
 (#match? @injection.content "^\"\\s*(<html|<!DOCTYPE)")
 (#set! injection.language "html"))

;; JSON in string literals (heuristic: starts with { or [)
((string_literal) @injection.content
 (#match? @injection.content "^\"\\s*[\\[{]")
 (#set! injection.language "json"))

;; ============================================================================
;; Foreign Function Interface (FFI)
;; ============================================================================

;; Extern function bodies (may contain C-like syntax)
((extern_function_declaration
  body: (block_expression) @injection.content)
 (#set! injection.language "c"))

;; Inline assembly (if supported)
((asm_block
  (asm_content) @injection.content)
 (#set! injection.language "asm"))

;; ============================================================================
;; Template/Macro Definitions
;; ============================================================================

;; Macro bodies (contain Simple syntax)
((macro_definition
  body: (macro_body) @injection.content)
 (#set! injection.language "simple"))

;; Template expansion
((template_expansion
  body: (template_body) @injection.content)
 (#set! injection.language "simple"))

;; ============================================================================
;; GPU Kernel Code
;; ============================================================================

;; GPU kernel blocks (may use shader-like syntax)
((kernel_block
  body: (kernel_body) @injection.content)
 (#set! injection.language "glsl"))

;; CUDA-style kernel
((cuda_kernel
  body: (kernel_body) @injection.content)
 (#set! injection.language "cuda"))

;; ============================================================================
;; Config File Embeddings
;; ============================================================================

;; TOML in config strings
((string_literal) @injection.content
 (#match? @injection.content "^\"\\[.*\\]")
 (#set! injection.language "toml"))

;; YAML in config strings
((string_literal) @injection.content
 (#match? @injection.content "^\".*:\\s")
 (#set! injection.language "yaml"))

;; ============================================================================
;; Comment Annotations
;; ============================================================================

;; TODO comments with structured format
((line_comment) @injection.content
 (#match? @injection.content "TODO|FIXME|HACK|XXX|NOTE")
 (#set! injection.language "comment"))

;; ============================================================================
;; Type-Specific String Injections
;; ============================================================================

;; Function calls with language hints
((call_expression
  function: (identifier) @_func
  arguments: (argument_list
    (string_literal) @injection.content))
 (#match? @_func "sql|execute_sql|query")
 (#set! injection.language "sql"))

((call_expression
  function: (identifier) @_func
  arguments: (argument_list
    (string_literal) @injection.content))
 (#match? @_func "html|render_html|to_html")
 (#set! injection.language "html"))

((call_expression
  function: (identifier) @_func
  arguments: (argument_list
    (string_literal) @injection.content))
 (#match? @_func "regex|re_match|pattern")
 (#set! injection.language "regex"))

;; ============================================================================
;; LaTeX Math in Strings
;; ============================================================================

;; LaTeX math expressions (enclosed in $ or $$)
((string_literal) @injection.content
 (#match? @injection.content "\\$.*\\$")
 (#set! injection.language "latex"))

;; ============================================================================
;; DSL Blocks (Domain-Specific Languages)
;; ============================================================================

;; Custom DSL blocks (example: query language)
((dsl_block
  (dsl_name) @_dsl_name
  (block_content) @injection.content)
 (#set! injection.language "custom"))

;; ============================================================================
;; Shebang Support (for .ssh scripts)
;; ============================================================================

;; Shebang line at top of file
((shebang) @injection.content
 (#set! injection.language "bash"))
