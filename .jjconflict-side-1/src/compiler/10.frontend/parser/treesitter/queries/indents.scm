;; indents.scm - Auto-Indentation Rules
;; Tree-sitter query file for automatic indentation
;; Enables: smart indent on newline, auto-dedent, alignment

;; ============================================================================
;; Indent (Increase Indentation)
;; ============================================================================

;; Function and Method Bodies
[
  (function_declaration)
  (method_declaration)
  (static_method_declaration)
  (mutable_method_declaration)
] @indent

;; Lambda Bodies
[
  (lambda_expression)
  (backslash_lambda)
  (pipe_lambda)
] @indent

;; Type Definition Bodies
[
  (class_declaration)
  (struct_declaration)
  (enum_declaration)
  (union_declaration)
  (trait_declaration)
  (mixin_declaration)
  (impl_block)
  (actor_declaration)
  (unit_declaration)
] @indent

;; Module Blocks
(module_declaration) @indent

;; Control Flow Blocks
[
  (if_expression)
  (elif_clause)
  (else_clause)
  (match_expression)
  (match_arm)
  (for_expression)
  (while_expression)
  (loop_expression)
] @indent

;; Exception Handling
[
  (try_expression)
  (catch_clause)
  (finally_clause)
] @indent

;; BDD Blocks
[
  (feature_declaration)
  (scenario_declaration)
  (given_step)
  (when_step)
  (then_step)
  (and_then_step)
  (it_block)
  (slow_it_block)
  (describe_block)
  (context_block)
] @indent

;; Contract Blocks
[
  (requires_clause)
  (ensures_clause)
  (invariant_declaration)
  (out_block)
  (out_err_block)
  (calc_block)
  (calc_step)
] @indent

;; AOP Blocks
[
  (aspect_declaration)
  (advice_declaration)
  (pointcut_declaration)
  (mock_declaration)
] @indent

;; Collection Literals (multi-line)
[
  (array_literal)
  (dict_literal)
  (struct_literal)
  (tuple_literal)
  (set_literal)
] @indent

;; Block Expressions
(block_expression) @indent

;; Call Expressions (multi-line)
(call_expression
  arguments: (argument_list) @indent)

(method_call_expression
  arguments: (argument_list) @indent)

;; Parameter Lists (multi-line)
(parameter_list) @indent

;; Type Parameter Lists
(type_parameter_list) @indent

;; ============================================================================
;; Dedent (Decrease Indentation)
;; ============================================================================

;; Closing Braces
"}" @dedent

;; Dedent Tokens (Python-style indentation)
(dedent) @dedent

;; Closing Brackets and Parens (when on own line)
"]" @dedent
")" @dedent

;; ============================================================================
;; Align (Align to Specific Column)
;; ============================================================================

;; Binary Operators - align operands
(binary_expression
  operator: (_) @align)

;; Assignment Operators - align right-hand side
(assignment_expression
  "=" @align)

(val_declaration
  "=" @align)

(var_declaration
  "=" @align)

;; Dictionary Colons - align values
(dict_entry
  ":" @align)

;; Type Annotations - align types
(type_annotation
  ":" @align)

;; Return Type Arrows - align return types
(function_signature
  "->" @align)

;; Match Arms - align bodies
(match_arm
  "=>" @align)

;; ============================================================================
;; Branch (Same Indentation Level)
;; ============================================================================

;; elif/else clauses (same level as if)
(elif_clause) @branch
(else_clause) @branch

;; Match case arms (same level as each other)
(match_arm) @branch

;; Catch/finally (same level as try)
(catch_clause) @branch
(finally_clause) @branch

;; ============================================================================
;; Ignore (Preserve User Indentation)
;; ============================================================================

;; Comments - preserve indentation
[
  (line_comment)
  (block_comment)
  (doc_comment)
] @ignore

;; String Literals - preserve content
[
  (string_literal)
  (raw_string_literal)
  (interpolated_string)
] @ignore

;; Empty Lines - preserve
(empty_line) @ignore

;; ============================================================================
;; Continue (Next Line Continuation)
;; ============================================================================

;; Binary operators at end of line - continue on next line
(binary_expression
  left: (_)
  operator: (_) @continue)

;; Pipeline operators - continue pipeline
[
  "|>"
  ">>"
  "<<"
  "~>"
  "//"
] @continue

;; Member access chains - continue chain
(member_expression
  "." @continue)

;; Optional chaining - continue chain
(optional_chain
  "?." @continue)

;; Multi-line strings - backslash at end
"\\" @continue
  (#match? @continue "\\\\$")

;; Comma-separated items - continue list
"," @continue

;; ============================================================================
;; Triggers (Characters that trigger auto-indent)
;; ============================================================================

;; Colon triggers indent (after if, fn, class, etc.)
":" @indent.trigger

;; Closing braces trigger dedent
"}" @dedent.trigger
"]" @dedent.trigger
")" @dedent.trigger

;; Return/break/continue trigger smart indent
[
  "return"
  "break"
  "continue"
  "yield"
] @indent.trigger

;; ============================================================================
;; Zero-Indent (No Indentation)
;; ============================================================================

;; Top-level declarations
(source_file
  [
    (function_declaration)
    (class_declaration)
    (struct_declaration)
    (enum_declaration)
    (trait_declaration)
    (module_declaration)
    (import_declaration)
    (use_declaration)
    (export_declaration)
    (const_declaration)
    (static_declaration)
  ] @zero_indent)

;; ============================================================================
;; Special Cases
;; ============================================================================

;; Suspend operators (if~, while~, etc.) - same indent rules as non-suspend
[
  "if~"
  "while~"
  "for~"
  "match~"
] @indent

;; Anonymous functions in arguments - indent body
(argument_list
  (lambda_expression) @indent)

;; Chained method calls - indent continuation
(member_expression
  object: (member_expression) @indent.continue)

;; Long type annotations - indent generic arguments
(type_identifier
  (type_arguments) @indent)

;; Multi-line conditions - indent continuation
(if_expression
  condition: (_) @indent.continue
    (#match? @indent.continue "\\n"))

(while_expression
  condition: (_) @indent.continue
    (#match? @indent.continue "\\n"))

;; ============================================================================
;; Embedded Languages (preserve their indentation)
;; ============================================================================

;; SQL blocks - preserve SQL indentation
(sql_block) @ignore

;; HTML blocks - preserve HTML indentation
(html_block) @ignore

;; Other embedded language blocks
[
  (sh_block)
  (md_block)
  (json_block)
  (yaml_block)
  (toml_block)
  (re_block)
  (css_block)
  (js_block)
  (py_block)
] @ignore

;; ============================================================================
;; Array/Dict Literal Alignment
;; ============================================================================

;; Array elements - align vertically
(array_literal
  (element_list
    (_) @align.element))

;; Dict entries - align keys and values
(dict_literal
  (dict_entry_list
    (dict_entry) @align.entry))

;; Struct fields - align field assignments
(struct_literal
  (field_list
    (field_assignment) @align.field))

;; ============================================================================
;; Function Call Alignment
;; ============================================================================

;; Named arguments - align names and values
(call_expression
  arguments: (argument_list
    (named_argument) @align.argument))

;; ============================================================================
;; Pattern Matching Alignment
;; ============================================================================

;; Match arms - align patterns and bodies
(match_expression
  (match_body
    (match_arm
      pattern: (_) @align.pattern
      body: (_) @align.body)))

;; ============================================================================
;; Type Definition Alignment
;; ============================================================================

;; Struct fields - align names and types
(struct_body
  (field_declaration
    name: (_) @align.field_name
    type: (_) @align.field_type))

;; Enum variants - align names
(enum_body
  (enum_variant
    name: (_) @align.variant))

;; ============================================================================
;; Conditional Expression Alignment
;; ============================================================================

;; Ternary-style expressions - align branches
(if_expression
  condition: (_) @align.condition
  consequence: (_) @align.consequence
  alternative: (_) @align.alternative)

;; ============================================================================
;; Pipeline Alignment
;; ============================================================================

;; Long pipelines - align stages
(pipeline_expression
  left: (_) @align.pipeline_left
  operator: (_)
  right: (_) @align.pipeline_right)

;; ============================================================================
;; Contract Alignment
;; ============================================================================

;; Requires/ensures clauses - align conditions
(requires_clause
  (condition_list
    (_) @align.condition))

(ensures_clause
  (condition_list
    (_) @align.condition))

;; Calc steps - align equations
(calc_block
  (calc_body
    (calc_step
      left: (_) @align.calc_left
      right: (_) @align.calc_right)))

;; ============================================================================
;; BDD Alignment
;; ============================================================================

;; Examples table - align columns
(examples_table
  (table_row
    (table_cell) @align.table_cell))

;; Step patterns - align parameter placeholders
(step_pattern
  (step_parameter) @align.parameter)

;; ============================================================================
;; Import Alignment
;; ============================================================================

;; Use declarations - align imported symbols
(use_declaration
  (use_list
    (use_item) @align.import))

;; ============================================================================
;; Attribute/Decorator Alignment
;; ============================================================================

;; Attributes above declarations - same indent as declaration
(attribute) @branch

;; Decorators - same indent as decorated item
(decorator) @branch
