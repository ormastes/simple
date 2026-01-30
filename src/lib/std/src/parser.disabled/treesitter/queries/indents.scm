; Tree-sitter Indentation Queries for Simple Language
; Defines indentation rules for auto-formatting

; ============================================================================
; Indent - Increase indentation
; ============================================================================

; Function/method bodies
(function_def
  body: (block) @indent.begin)

(method_def
  body: (block) @indent.begin)

(static_method_def
  body: (block) @indent.begin)

; Lambda bodies
(fn_lambda
  body: (block) @indent.begin)

(backslash_lambda
  body: (block) @indent.begin)

(pipe_lambda
  body: (block) @indent.begin)

; Class/struct/enum bodies
(class_def
  body: (class_block) @indent.begin)

(struct_def
  body: (struct_block) @indent.begin)

(enum_def
  body: (enum_block) @indent.begin)

(union_def
  body: (enum_block) @indent.begin)

(trait_def
  body: (trait_block) @indent.begin)

(mixin_def
  body: (trait_block) @indent.begin)

(actor_def
  body: (class_block) @indent.begin)

; Impl blocks
(impl_def
  body: (impl_block) @indent.begin)

; Module blocks
(mod_def
  body: (block) @indent.begin)

; Mock blocks
(mock_def
  body: (mock_block) @indent.begin)

; If/elif/else
(if_stmt
  body: (block) @indent.begin)

(elif_clause
  body: (block) @indent.begin)

(else_clause
  body: (block) @indent.begin)

; Match statements
(match_stmt
  body: (match_block) @indent.begin)

(match_case
  body: (_) @indent.begin)

; Loops
(for_stmt
  body: (block) @indent.begin)

(while_stmt
  body: (block) @indent.begin)

(loop_stmt
  body: (block) @indent.begin)

; BDD blocks
(feature_def
  body: (feature_block) @indent.begin)

(scenario_def
  body: (scenario_block) @indent.begin)

(given_step
  body: (block) @indent.begin)

(when_step
  body: (block) @indent.begin)

(then_step
  body: (block) @indent.begin)

(and_then_step
  body: (block) @indent.begin)

(examples_block
  body: (examples_table) @indent.begin)

; Contract blocks
(out_stmt
  body: (block) @indent.begin)

(out_err_stmt
  body: (block) @indent.begin)

(calc_block
  body: (calc_steps) @indent.begin)

; Collection literals
(array_literal) @indent.begin

(dict_literal) @indent.begin

(struct_literal) @indent.begin

(tuple_literal) @indent.begin

; Parenthesized expressions (multi-line)
(paren_expr) @indent.begin

; Multi-line call arguments
(call_expr
  arguments: (argument_list) @indent.begin)

; Multi-line function parameters
(function_def
  parameters: (parameter_list) @indent.begin)

; ============================================================================
; Dedent - Decrease indentation (end of block)
; ============================================================================

; Block end markers
(block
  "}" @indent.end)

; Dedent token (Python-style)
(dedent) @indent.end

; ============================================================================
; Align - Align to specific tokens
; ============================================================================

; Align binary operators
(binary_expr
  operator: (_) @indent.align)

; Align assignment operators
(val_stmt
  "=" @indent.align)

(var_stmt
  "=" @indent.align)

; Align dictionary entries
(dict_entry
  ":" @indent.align)

; Align function parameters (when multi-line)
(parameter
  ":" @indent.align)

; Align type annotations
(_
  "->" @indent.align)

; ============================================================================
; Branch - Alternative indentation points
; ============================================================================

; Elif/else at same level as if
(elif_clause) @indent.branch

(else_clause) @indent.branch

; Match cases at same level
(match_case) @indent.branch

; ============================================================================
; Ignore - Don't change indentation
; ============================================================================

; Comments should preserve their indentation
(line_comment) @indent.ignore

(block_comment) @indent.ignore

(doc_comment) @indent.ignore

; String literals should preserve formatting
(string_literal) @indent.ignore

(raw_string_literal) @indent.ignore

(fstring_literal) @indent.ignore

; Empty lines
(newline) @indent.ignore

; ============================================================================
; Special Cases - Context-specific indentation
; ============================================================================

; Continuation lines (operators at end of line)
(binary_expr
  left: (_)
  operator: (_) @indent.continue)

; Chained method calls
(field_expr
  "." @indent.continue)

; Multi-line string concatenation
((string_literal) @indent.continue
  (#match? @indent.continue ".*\\\\$"))

; ============================================================================
; Auto-indent Triggers - When to trigger auto-indent
; ============================================================================

; Trigger on colon (start of block)
":" @indent.trigger

; Trigger on closing brace
"}" @indent.trigger

; Trigger on closing bracket
"]" @indent.trigger

; Trigger on closing paren
")" @indent.trigger

; Trigger on newline after certain keywords
(return_stmt) @indent.trigger

(break_stmt) @indent.trigger

(continue_stmt) @indent.trigger

; ============================================================================
; Zero-indent - No indentation at all
; ============================================================================

; Top-level declarations start at column 0
(function_def) @indent.zero

(class_def) @indent.zero

(struct_def) @indent.zero

(enum_def) @indent.zero

(union_def) @indent.zero

(trait_def) @indent.zero

(impl_def) @indent.zero

(mod_def) @indent.zero

(import_stmt) @indent.zero

(use_stmt) @indent.zero

(export_stmt) @indent.zero

(common_stmt) @indent.zero
