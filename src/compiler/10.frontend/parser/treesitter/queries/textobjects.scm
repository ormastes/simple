;; textobjects.scm - Semantic Code Selection and Navigation
;; Tree-sitter query file for defining semantic text objects
;; Enables: smart selection, jump to next/previous function/class, etc.

;; ============================================================================
;; Functions & Methods
;; ============================================================================

;; Function - entire function with signature
(function_declaration) @function.outer

;; Function - body only
(function_declaration
  body: (block_expression) @function.inner)

;; Method - entire method with signature
(method_declaration) @method.outer
(static_method_declaration) @method.outer
(mutable_method_declaration) @method.outer

;; Method - body only
(method_declaration
  body: (block_expression) @method.inner)

(static_method_declaration
  body: (block_expression) @method.inner)

(mutable_method_declaration
  body: (block_expression) @method.inner)

;; ============================================================================
;; Classes & Types
;; ============================================================================

;; Class - entire class definition
(class_declaration) @class.outer
(struct_declaration) @class.outer
(enum_declaration) @class.outer
(union_declaration) @class.outer
(trait_declaration) @class.outer
(actor_declaration) @class.outer

;; Class - body only
(class_declaration
  body: (class_body) @class.inner)

(struct_declaration
  body: (struct_body) @class.inner)

(enum_declaration
  body: (enum_body) @class.inner)

(union_declaration
  body: (union_body) @class.inner)

(trait_declaration
  body: (trait_body) @class.inner)

(actor_declaration
  body: (actor_body) @class.inner)

;; Type definitions (generic)
(class_declaration) @type.outer
(struct_declaration) @type.outer
(enum_declaration) @type.outer
(union_declaration) @type.outer
(trait_declaration) @type.outer

;; ============================================================================
;; Blocks
;; ============================================================================

;; Block - entire block with braces/indentation
(block_expression) @block.outer

;; Block - content only (excluding delimiters)
(block_expression
  (statement_list) @block.inner)

;; ============================================================================
;; Conditionals
;; ============================================================================

;; Conditional - entire if/elif/else structure
(if_expression) @conditional.outer

;; Conditional - condition + body
(if_expression
  condition: (_) @conditional.condition
  consequence: (_) @conditional.consequence)

(if_expression
  alternative: (_) @conditional.alternative)

;; Conditional - inner (body only)
(if_expression
  consequence: (block_expression) @conditional.inner)

;; Match expression - entire match
(match_expression) @conditional.outer

;; Match - arms
(match_arm) @conditional.arm

;; Match - pattern and body
(match_arm
  pattern: (_) @conditional.pattern
  body: (_) @conditional.body)

;; ============================================================================
;; Loops
;; ============================================================================

;; Loop - entire loop structure
(for_expression) @loop.outer
(while_expression) @loop.outer
(loop_expression) @loop.outer

;; Loop - body only
(for_expression
  body: (block_expression) @loop.inner)

(while_expression
  body: (block_expression) @loop.inner)

(loop_expression
  body: (block_expression) @loop.inner)

;; Loop - condition
(for_expression
  iterator: (_) @loop.iterator)

(while_expression
  condition: (_) @loop.condition)

;; ============================================================================
;; Parameters & Arguments
;; ============================================================================

;; Parameter - single parameter
(parameter) @parameter.outer

;; Parameter list - all parameters
(parameter_list) @parameter.list

;; Parameter - name only
(parameter
  name: (identifier) @parameter.name)

;; Parameter - type only
(parameter
  type: (_) @parameter.type)

;; Argument - single argument
(argument) @argument.outer

;; Argument list - all arguments
(argument_list) @call.arguments

;; ============================================================================
;; Assignments
;; ============================================================================

;; Assignment - entire assignment
(assignment_expression) @assignment.outer
(val_declaration) @assignment.outer
(var_declaration) @assignment.outer

;; Assignment - left-hand side
(assignment_expression
  left: (_) @assignment.lhs)

(val_declaration
  name: (identifier) @assignment.lhs)

(var_declaration
  name: (identifier) @assignment.lhs)

;; Assignment - right-hand side
(assignment_expression
  right: (_) @assignment.rhs)

(val_declaration
  value: (_) @assignment.rhs)

(var_declaration
  value: (_) @assignment.rhs)

;; ============================================================================
;; Lambdas
;; ============================================================================

;; Lambda - entire lambda expression
(lambda_expression) @lambda.outer
(backslash_lambda) @lambda.outer
(pipe_lambda) @lambda.outer

;; Lambda - body only
(lambda_expression
  body: (_) @lambda.inner)

(backslash_lambda
  body: (_) @lambda.inner)

(pipe_lambda
  body: (_) @lambda.inner)

;; Lambda - parameters
(lambda_expression
  parameters: (lambda_parameter_list) @lambda.parameters)

;; ============================================================================
;; Calls
;; ============================================================================

;; Call - entire call expression
(call_expression) @call.outer
(method_call_expression) @call.outer
(static_call_expression) @call.outer

;; Call - callee (function being called)
(call_expression
  function: (_) @call.callee)

;; Call - method name
(method_call_expression
  method: (identifier) @call.method)

(static_call_expression
  method: (identifier) @call.method)

;; Call - receiver/object
(method_call_expression
  object: (_) @call.receiver)

(static_call_expression
  type: (_) @call.receiver)

;; Call - arguments
(call_expression
  arguments: (argument_list) @call.arguments)

(method_call_expression
  arguments: (argument_list) @call.arguments)

;; ============================================================================
;; Operators
;; ============================================================================

;; Binary operation - entire expression
(binary_expression) @operator.binary

;; Binary operation - left operand
(binary_expression
  left: (_) @operator.left)

;; Binary operation - right operand
(binary_expression
  right: (_) @operator.right)

;; Binary operation - operator itself
(binary_expression
  operator: (_) @operator.op)

;; Unary operation - entire expression
(unary_expression) @operator.unary

;; Unary operation - operand
(unary_expression
  operand: (_) @operator.operand)

;; Pipeline expressions
(pipeline_expression) @operator.pipeline

;; ============================================================================
;; Literals
;; ============================================================================

;; String literals
(string_literal) @string.outer
(raw_string_literal) @string.outer
(interpolated_string) @string.outer

;; Number literals
(integer_literal) @number.outer
(float_literal) @number.outer

;; Collection literals
(array_literal) @collection.outer
(dict_literal) @collection.outer
(struct_literal) @collection.outer
(tuple_literal) @collection.outer
(set_literal) @collection.outer

;; Collection - content only
(array_literal
  (element_list) @collection.inner)

(dict_literal
  (dict_entry_list) @collection.inner)

;; ============================================================================
;; Comments
;; ============================================================================

;; Comment - entire comment
(line_comment) @comment.outer
(block_comment) @comment.outer
(doc_comment) @comment.outer

;; Comment - content only (excluding delimiters)
(doc_comment
  (doc_content) @comment.inner)

;; ============================================================================
;; BDD/Testing
;; ============================================================================

;; Feature - entire feature definition
(feature_declaration) @test.feature.outer

;; Feature - body only
(feature_declaration
  body: (feature_body) @test.feature.inner)

;; Scenario - entire scenario
(scenario_declaration) @test.scenario.outer

;; Scenario - body only
(scenario_declaration
  body: (scenario_body) @test.scenario.inner)

;; Test steps - individual steps
(given_step) @test.step.outer
(when_step) @test.step.outer
(then_step) @test.step.outer
(and_then_step) @test.step.outer

;; Test step - body only
(given_step
  body: (block_expression) @test.step.inner)

(when_step
  body: (block_expression) @test.step.inner)

(then_step
  body: (block_expression) @test.step.inner)

;; Examples table
(examples_declaration) @test.examples.outer

(examples_declaration
  table: (examples_table) @test.examples.inner)

;; it/slow_it blocks
(it_block) @test.it.outer
(slow_it_block) @test.it.outer

(it_block
  body: (block_expression) @test.it.inner)

;; ============================================================================
;; AOP (Aspect-Oriented Programming)
;; ============================================================================

;; Pointcut expression
(pointcut_expression) @aop.pointcut

;; Advice declaration
(advice_declaration) @aop.advice.outer

(advice_declaration
  body: (block_expression) @aop.advice.inner)

;; Aspect declaration
(aspect_declaration) @aop.aspect.outer

(aspect_declaration
  body: (aspect_body) @aop.aspect.inner)

;; Dependency injection binding
(bind_declaration) @aop.binding

;; Architecture rule
(forbid_rule) @aop.rule
(allow_rule) @aop.rule

;; Mock definition
(mock_declaration) @aop.mock.outer

(mock_declaration
  body: (mock_body) @aop.mock.inner)

;; ============================================================================
;; Contracts
;; ============================================================================

;; Precondition (requires)
(requires_clause) @contract.precondition

;; Postcondition (ensures/out)
(ensures_clause) @contract.postcondition
(out_block) @contract.postcondition
(out_err_block) @contract.postcondition

;; Invariant
(invariant_declaration) @contract.invariant

;; Quantifier expressions
(forall_expression) @contract.quantifier
(exists_expression) @contract.quantifier

;; Calc block (proof)
(calc_block) @contract.proof.outer

(calc_block
  body: (calc_body) @contract.proof.inner)

;; Calc step
(calc_step) @contract.proof.step

;; ============================================================================
;; Imports & Exports
;; ============================================================================

;; Import statement
(use_declaration) @import.outer
(import_declaration) @import.outer

;; Import - path only
(use_declaration
  path: (module_path) @import.path)

;; Export statement
(export_declaration) @export.outer

;; ============================================================================
;; Type Annotations
;; ============================================================================

;; Type annotation - entire annotation
(type_annotation) @type.annotation

;; Type annotation - type only
(type_annotation
  type: (_) @type.type)

;; Generic parameters
(type_parameter_list) @type.parameters

;; Generic arguments
(type_arguments) @type.arguments

;; ============================================================================
;; Scopes (Generic)
;; ============================================================================

;; Any scope boundary
(function_declaration) @scope
(method_declaration) @scope
(class_declaration) @scope
(impl_block) @scope
(block_expression) @scope
(lambda_expression) @scope
(if_expression) @scope
(match_expression) @scope
(for_expression) @scope
(while_expression) @scope

;; ============================================================================
;; Statements
;; ============================================================================

;; Statement - single statement
(statement) @statement.outer

;; Return statement
(return_statement) @statement.return

;; Break/continue statements
(break_statement) @statement.break
(continue_statement) @statement.continue

;; Expression statement
(expression_statement) @statement.expression

;; ============================================================================
;; Fields & Properties
;; ============================================================================

;; Field declaration
(field_declaration) @field.outer

;; Field - name only
(field_declaration
  name: (identifier) @field.name)

;; Field - type only
(field_declaration
  type: (_) @field.type)

;; Field - initializer
(field_declaration
  value: (_) @field.value)

;; Property access
(member_expression) @property.access

(member_expression
  property: (identifier) @property.name)

;; ============================================================================
;; Module & Namespace
;; ============================================================================

;; Module declaration
(module_declaration) @module.outer

;; Module - body only
(module_declaration
  body: (module_body) @module.inner)

;; ============================================================================
;; Exception Handling
;; ============================================================================

;; Try expression
(try_expression) @exception.try.outer

(try_expression
  body: (block_expression) @exception.try.inner)

;; Catch clause
(catch_clause) @exception.catch.outer

(catch_clause
  body: (block_expression) @exception.catch.inner)

;; Finally clause
(finally_clause) @exception.finally.outer

(finally_clause
  body: (block_expression) @exception.finally.inner)

;; ============================================================================
;; Embedded Languages
;; ============================================================================

;; SQL block
(sql_block) @embedded.sql

;; Shell block
(sh_block) @embedded.shell

;; HTML block
(html_block) @embedded.html

;; Regex block
(re_block) @embedded.regex

;; Math block
(math_block) @embedded.math

;; ============================================================================
;; Special Constructs
;; ============================================================================

;; Pattern matching patterns
(pattern) @pattern.outer

;; Struct pattern
(struct_pattern) @pattern.struct

;; Tuple pattern
(tuple_pattern) @pattern.tuple

;; Array pattern
(array_pattern) @pattern.array

;; Range expression
(range_expression) @range.outer

;; Slice expression
(slice_expression) @slice.outer

;; Index expression
(index_expression) @index.outer
