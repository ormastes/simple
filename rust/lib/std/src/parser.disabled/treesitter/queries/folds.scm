; Tree-sitter Folding Queries for Simple Language
; Defines foldable regions for code editors

; ============================================================================
; Declarations - Foldable declarations
; ============================================================================

; Function definitions
(function_def
  body: (block) @fold)

(function_declaration
  body: (block) @fold)

; Method definitions
(method_def
  body: (block) @fold)

(static_method_def
  body: (block) @fold)

; Class definitions
(class_def
  body: (class_block) @fold)

(class_declaration
  body: (_) @fold)

; Struct definitions
(struct_def
  body: (struct_block) @fold)

; Enum definitions
(enum_def
  body: (enum_block) @fold)

(enum_declaration
  body: (_) @fold)

; Union definitions
(union_def
  body: (enum_block) @fold)

; Trait definitions
(trait_def
  body: (trait_block) @fold)

(trait_declaration
  body: (_) @fold)

; Mixin definitions
(mixin_def
  body: (trait_block) @fold)

; Impl blocks
(impl_def
  body: (impl_block) @fold)

; Actor definitions
(actor_def
  body: (class_block) @fold)

; Module definitions
(mod_def
  body: (block) @fold)

; Mock definitions
(mock_def
  body: (mock_block) @fold)

; Unit family definitions
(unit_def
  body: (unit_variants) @fold)

; Handle pool definitions
(handle_pool_def
  body: (handle_pool_block) @fold)

; ============================================================================
; Control Flow - Foldable control structures
; ============================================================================

; If statements
(if_stmt
  body: (block) @fold)

(if_expression
  consequence: (_) @fold
  alternative: (_)? @fold)

; Match statements
(match_stmt
  body: (match_block) @fold)

(match_expression
  body: (_) @fold)

; For loops
(for_stmt
  body: (block) @fold)

(for_statement
  body: (_) @fold)

; While loops
(while_stmt
  body: (block) @fold)

(while_statement
  body: (_) @fold)

; Loop statements
(loop_stmt
  body: (block) @fold)

; ============================================================================
; Lambda Expressions - Foldable closures
; ============================================================================

; fn() lambdas with blocks
(fn_lambda
  body: (block) @fold)

; Backslash lambdas with blocks
(backslash_lambda
  body: (block) @fold)

; Pipe lambdas with blocks
(pipe_lambda
  body: (block) @fold)

; ============================================================================
; BDD/Gherkin - Foldable test structures
; ============================================================================

; Feature blocks
(feature_def
  body: (feature_block) @fold)

; Scenario blocks
(scenario_def
  body: (scenario_block) @fold)

; Given/When/Then steps
(given_step
  body: (block) @fold)

(when_step
  body: (block) @fold)

(then_step
  body: (block) @fold)

(and_then_step
  body: (block) @fold)

; Examples blocks
(examples_block
  body: (examples_table) @fold)

; ============================================================================
; Contracts - Foldable contract blocks
; ============================================================================

; Out blocks
(out_stmt
  body: (block) @fold)

; Out_err blocks
(out_err_stmt
  body: (block) @fold)

; Calc blocks
(calc_block
  body: (calc_steps) @fold)

; ============================================================================
; Collections - Foldable literals
; ============================================================================

; Array literals
(array_literal) @fold

; Dict literals
(dict_literal) @fold

; Struct literals
(struct_literal) @fold

; ============================================================================
; Comments - Foldable comment blocks
; ============================================================================

; Block comments
(block_comment) @fold

; Doc comments
(doc_comment) @fold

; Consecutive line comments (folded together)
((line_comment)+) @fold
