;; folds.scm - Code Folding Regions
;; Tree-sitter query file for defining foldable code regions
;; Enables: collapse/expand blocks in editors

;; ============================================================================
;; Function and Method Bodies
;; ============================================================================

(function_declaration
  body: (block_expression) @fold)

(method_declaration
  body: (block_expression) @fold)

(static_method_declaration
  body: (block_expression) @fold)

(mutable_method_declaration
  body: (block_expression) @fold)

;; ============================================================================
;; Type Definition Bodies
;; ============================================================================

(class_declaration
  body: (class_body) @fold)

(struct_declaration
  body: (struct_body) @fold)

(enum_declaration
  body: (enum_body) @fold)

(union_declaration
  body: (union_body) @fold)

(trait_declaration
  body: (trait_body) @fold)

(mixin_declaration
  body: (mixin_body) @fold)

(impl_block
  body: (impl_body) @fold)

(actor_declaration
  body: (actor_body) @fold)

;; Unit family definitions
(unit_declaration
  body: (unit_body) @fold)

;; Handle pool definitions
(handle_pool
  body: (pool_body) @fold)

;; ============================================================================
;; Module Blocks
;; ============================================================================

(module_declaration
  body: (module_body) @fold)

;; ============================================================================
;; Control Flow Blocks
;; ============================================================================

;; If/elif/else
(if_expression
  consequence: (block_expression) @fold)

(if_expression
  alternative: (block_expression) @fold)

(elif_clause
  consequence: (block_expression) @fold)

;; Match statements
(match_expression
  body: (match_body) @fold)

(match_arm
  body: (block_expression) @fold)

;; Loops
(for_expression
  body: (block_expression) @fold)

(while_expression
  body: (block_expression) @fold)

(loop_expression
  body: (block_expression) @fold)

;; ============================================================================
;; Lambda Expressions
;; ============================================================================

;; fn() lambda
(lambda_expression
  body: (block_expression) @fold)

;; Backslash lambda with block body
(backslash_lambda
  body: (block_expression) @fold)

;; Pipe lambda with block body
(pipe_lambda
  body: (block_expression) @fold)

;; ============================================================================
;; BDD/Testing Blocks
;; ============================================================================

;; Feature blocks
(feature_declaration
  body: (feature_body) @fold)

;; Scenario blocks
(scenario_declaration
  body: (scenario_body) @fold)

;; Test steps
(given_step
  body: (block_expression) @fold)

(when_step
  body: (block_expression) @fold)

(then_step
  body: (block_expression) @fold)

(and_then_step
  body: (block_expression) @fold)

;; Examples tables
(examples_declaration
  table: (examples_table) @fold)

;; it/slow_it blocks
(it_block
  body: (block_expression) @fold)

(slow_it_block
  body: (block_expression) @fold)

;; describe/context blocks
(describe_block
  body: (block_expression) @fold)

(context_block
  body: (block_expression) @fold)

;; ============================================================================
;; Contract Blocks
;; ============================================================================

;; Out blocks
(out_block
  body: (block_expression) @fold)

;; Out_err blocks
(out_err_block
  body: (block_expression) @fold)

;; Calc blocks (proof steps)
(calc_block
  body: (calc_body) @fold)

;; Requires/Ensures blocks
(requires_clause
  body: (block_expression) @fold)

(ensures_clause
  body: (block_expression) @fold)

;; Invariant blocks
(invariant_declaration
  body: (block_expression) @fold)

;; ============================================================================
;; Mock Blocks
;; ============================================================================

(mock_declaration
  body: (mock_body) @fold)

;; ============================================================================
;; Aspect-Oriented Programming
;; ============================================================================

;; Aspect definitions
(aspect_declaration
  body: (aspect_body) @fold)

;; Advice definitions
(advice_declaration
  body: (block_expression) @fold)

;; Pointcut definitions with complex bodies
(pointcut_declaration
  body: (pointcut_body) @fold)

;; ============================================================================
;; Collection Literals
;; ============================================================================

;; Array literals (multi-line)
(array_literal) @fold

;; Dictionary literals (multi-line)
(dict_literal) @fold

;; Struct literals (multi-line)
(struct_literal) @fold

;; Tuple literals (multi-line)
(tuple_literal) @fold

;; Set literals (multi-line)
(set_literal) @fold

;; ============================================================================
;; Comments
;; ============================================================================

;; Block comments
(block_comment) @fold

;; Doc comments (multi-line)
(doc_comment) @fold

;; Consecutive line comments (3+ lines)
(comment_group) @fold

;; ============================================================================
;; Exception Handling
;; ============================================================================

;; Try blocks
(try_expression
  body: (block_expression) @fold)

;; Catch blocks
(catch_clause
  body: (block_expression) @fold)

;; Finally blocks
(finally_clause
  body: (block_expression) @fold)

;; ============================================================================
;; String Literals
;; ============================================================================

;; Multi-line string literals
(string_literal) @fold
  (#match? @fold "\\n")

;; Multi-line raw strings
(raw_string_literal) @fold
  (#match? @fold "\\n")

;; ============================================================================
;; Import Groups
;; ============================================================================

;; Multiple consecutive imports
(import_group) @fold

;; Multiple consecutive use statements
(use_group) @fold

;; ============================================================================
;; Special Embedded Blocks
;; ============================================================================

;; SQL blocks
(sql_block) @fold

;; Shell script blocks
(sh_block) @fold

;; HTML blocks
(html_block) @fold

;; Markdown blocks
(md_block) @fold

;; JSON blocks
(json_block) @fold

;; YAML blocks
(yaml_block) @fold

;; TOML blocks
(toml_block) @fold

;; Regex blocks
(re_block) @fold

;; Math blocks
(math_block) @fold

;; ============================================================================
;; Generic Blocks
;; ============================================================================

;; Any block expression (fallback)
(block_expression) @fold

;; Braced blocks
("{" "}" @fold.bracket)

;; Bracketed expressions
("[" "]" @fold.bracket)

;; Parenthesized expressions (only if multi-line)
("(" ")" @fold.bracket)

;; ============================================================================
;; Fold Markers (Custom)
;; ============================================================================

;; Regions marked with comments (e.g., // region ... // endregion)
(region_comment) @fold

;; Custom fold markers
(comment) @fold.marker
  (#match? @fold.marker "fold|region|BEGIN|END")

;; ============================================================================
;; Type Bodies with Multiple Members
;; ============================================================================

;; Enum variants (collapse entire variant list)
(enum_body
  (enum_variant_list) @fold)

;; Struct fields (collapse field list)
(struct_body
  (field_list) @fold)

;; Trait method signatures (collapse method list)
(trait_body
  (trait_item_list) @fold)

;; ============================================================================
;; Parameter Lists (long function signatures)
;; ============================================================================

;; Function parameter lists (only if multi-line)
(function_declaration
  parameters: (parameter_list) @fold)
  (#match? @fold "\\n")

;; Method parameter lists
(method_declaration
  parameters: (parameter_list) @fold)
  (#match? @fold "\\n")

;; ============================================================================
;; Call Arguments (long calls)
;; ============================================================================

;; Function call arguments (only if multi-line)
(call_expression
  arguments: (argument_list) @fold)
  (#match? @fold "\\n")

;; Method call arguments
(method_call_expression
  arguments: (argument_list) @fold)
  (#match? @fold "\\n")

;; ============================================================================
;; Chain Expressions (long method chains)
;; ============================================================================

;; Method chaining (fold multiple chained calls)
(chain_expression) @fold
  (#match? @fold "\\n.*\\n")

;; ============================================================================
;; Pipeline Expressions
;; ============================================================================

;; Long pipelines (|>, >>, etc.)
(pipeline_expression) @fold
  (#match? @fold "\\n")

;; ============================================================================
;; Match Arms (individual arms in large matches)
;; ============================================================================

;; Each match arm can be folded
(match_arm) @fold

;; ============================================================================
;; Indentation-Based Folding (Python-style)
;; ============================================================================

;; Fold based on indentation level changes
;; (This is editor-specific, some editors support this automatically)
