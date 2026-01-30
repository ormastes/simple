; Tree-sitter Text Objects Queries for Simple Language
; Defines semantic text objects for code navigation and manipulation
; Used by editors like Neovim with nvim-treesitter-textobjects

; ============================================================================
; Functions - Navigate/select functions
; ============================================================================

; Function outer (including signature)
(function_def) @function.outer

(function_declaration) @function.outer

; Function inner (body only)
(function_def
  body: (block) @function.inner)

(function_declaration
  body: (block) @function.inner)

; ============================================================================
; Methods - Navigate/select methods
; ============================================================================

; Method outer
(method_def) @method.outer

(static_method_def) @method.outer

; Method inner
(method_def
  body: (block) @method.inner)

(static_method_def
  body: (block) @method.inner)

; ============================================================================
; Classes - Navigate/select class definitions
; ============================================================================

; Class outer
(class_def) @class.outer

(class_declaration) @class.outer

; Class inner (body only)
(class_def
  body: (class_block) @class.inner)

; ============================================================================
; Blocks - Navigate/select code blocks
; ============================================================================

; Block outer (including braces/indentation)
(block) @block.outer

; Block inner (content only)
(block) @block.inner

; ============================================================================
; Conditionals - Navigate/select if/match statements
; ============================================================================

; If statement outer
(if_stmt) @conditional.outer

(if_expression) @conditional.outer

; If statement inner (condition + bodies)
(if_stmt
  body: (_) @conditional.inner)

; Match statement outer
(match_stmt) @conditional.outer

(match_expression) @conditional.outer

; Match arm
(match_case) @conditional.arm

; ============================================================================
; Loops - Navigate/select loop constructs
; ============================================================================

; For loop outer
(for_stmt) @loop.outer

(for_statement) @loop.outer

; For loop inner
(for_stmt
  body: (block) @loop.inner)

; While loop outer
(while_stmt) @loop.outer

(while_statement) @loop.outer

; While loop inner
(while_stmt
  body: (block) @loop.inner)

; Loop statement outer
(loop_stmt) @loop.outer

; Loop statement inner
(loop_stmt
  body: (block) @loop.inner)

; ============================================================================
; Parameters - Navigate/select function parameters
; ============================================================================

; Parameter outer
(parameter) @parameter.outer

; Parameter list
(parameter_list) @parameter.list

; ============================================================================
; Arguments - Navigate/select function call arguments
; ============================================================================

; Argument in call
(call_expr
  arguments: (argument_list) @call.arguments)

; Single argument
(argument_list
  (_) @argument.outer)

; ============================================================================
; Comments - Navigate/select comments
; ============================================================================

; Line comment
(line_comment) @comment.outer

; Block comment
(block_comment) @comment.outer

; Doc comment
(doc_comment) @comment.documentation

; ============================================================================
; Statements - Navigate/select individual statements
; ============================================================================

; Any statement
(val_stmt) @statement.outer
(var_stmt) @statement.outer
(let_stmt) @statement.outer
(const_stmt) @statement.outer
(static_stmt) @statement.outer
(return_stmt) @statement.outer
(assert_stmt) @statement.outer
(assume_stmt) @statement.outer
(expression_stmt) @statement.outer

; ============================================================================
; Assignments - Navigate/select assignment statements
; ============================================================================

; Val/var assignments
(val_stmt) @assignment.outer
(var_stmt) @assignment.outer

; Assignment right-hand side
(val_stmt
  value: (_) @assignment.rhs)

(var_stmt
  value: (_) @assignment.rhs)

; Assignment left-hand side
(val_stmt
  pattern: (_) @assignment.lhs)

(var_stmt
  pattern: (_) @assignment.lhs)

; ============================================================================
; Lambda Expressions - Navigate/select closures
; ============================================================================

; Lambda outer
(fn_lambda) @lambda.outer
(backslash_lambda) @lambda.outer
(pipe_lambda) @lambda.outer

; Lambda inner (body only)
(fn_lambda
  body: (_) @lambda.inner)

(backslash_lambda
  body: (_) @lambda.inner)

(pipe_lambda
  body: (_) @lambda.inner)

; ============================================================================
; Types - Navigate/select type annotations
; ============================================================================

; Type definition outer
(type_alias_stmt) @type.outer
(union_def) @type.outer
(struct_def) @type.outer
(enum_def) @type.outer

; Type annotation
(parameter
  type: (_) @type.annotation)

; ============================================================================
; Patterns - Navigate/select pattern matching
; ============================================================================

; Pattern in match case
(match_case
  pattern: (_) @pattern.outer)

; Pattern in let binding
(val_stmt
  pattern: (_) @pattern.outer)

; ============================================================================
; Calls - Navigate/select function/method calls
; ============================================================================

; Call expression outer
(call_expr) @call.outer

; Call expression callee
(call_expr
  callee: (_) @call.callee)

; Method call outer
(field_expr
  value: (_)
  field: (_)) @call.method

; Static call outer
(static_call_expr) @call.static

; ============================================================================
; Operators - Navigate/select operator expressions
; ============================================================================

; Binary expression outer
(binary_expr) @operator.binary

; Binary expression left/right operands
(binary_expr
  left: (_) @operator.left
  right: (_) @operator.right)

; Unary expression outer
(unary_expr) @operator.unary

; ============================================================================
; Literals - Navigate/select literal values
; ============================================================================

; String literals
(string_literal) @string.outer
(raw_string_literal) @string.outer
(fstring_literal) @string.outer

; Number literals
(integer_literal) @number.outer
(typed_integer_literal) @number.outer
(float_literal) @number.outer
(typed_float_literal) @number.outer

; Collection literals
(array_literal) @collection.outer
(dict_literal) @collection.outer
(struct_literal) @collection.outer

; ============================================================================
; BDD/Testing - Navigate/select test structures
; ============================================================================

; Feature outer
(feature_def) @test.feature.outer

; Scenario outer
(scenario_def) @test.scenario.outer

; Test step outer
(given_step) @test.step.outer
(when_step) @test.step.outer
(then_step) @test.step.outer
(and_then_step) @test.step.outer

; ============================================================================
; AOP - Navigate/select AOP constructs
; ============================================================================

; Pointcut expression
(pointcut_expr) @aop.pointcut

; AOP statement outer
(on_stmt) @aop.advice
(bind_stmt) @aop.binding
(forbid_stmt) @aop.rule
(allow_stmt) @aop.rule

; Mock definition outer
(mock_def) @aop.mock.outer

; ============================================================================
; Contracts - Navigate/select contract constructs
; ============================================================================

; Contract statements
(requires_stmt) @contract.precondition
(ensures_stmt) @contract.postcondition
(out_stmt) @contract.postcondition
(out_err_stmt) @contract.postcondition
(invariant_stmt) @contract.invariant

; Quantifiers
(forall_stmt) @contract.quantifier
(exists_stmt) @contract.quantifier

; Calc block
(calc_block) @contract.proof

; ============================================================================
; Scope Movement - For jumping between scope boundaries
; ============================================================================

; All scopes
(block) @scope
(class_block) @scope
(struct_block) @scope
(enum_block) @scope
(trait_block) @scope
(impl_block) @scope
(mock_block) @scope
(feature_block) @scope
(scenario_block) @scope
