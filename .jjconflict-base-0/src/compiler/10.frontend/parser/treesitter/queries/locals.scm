;; locals.scm - Scope Tracking and Variable Resolution
;; Tree-sitter query file for LSP features: go-to-definition, find references, rename
;; Enables: variable resolution, scope analysis, shadowing detection

;; ============================================================================
;; Scope Definitions - Where new scopes begin
;; ============================================================================

;; Function and Method Scopes
(function_declaration) @local.scope
(method_declaration) @local.scope
(static_method_declaration) @local.scope
(mutable_method_declaration) @local.scope

;; Lambda Scopes
(lambda_expression) @local.scope
(backslash_lambda) @local.scope
(pipe_lambda) @local.scope

;; Type Definition Scopes
(class_declaration) @local.scope
(struct_declaration) @local.scope
(enum_declaration) @local.scope
(union_declaration) @local.scope
(trait_declaration) @local.scope
(mixin_declaration) @local.scope
(impl_block) @local.scope
(actor_declaration) @local.scope

;; Module Scope
(module_declaration) @local.scope

;; Mock Scope
(mock_declaration) @local.scope

;; Control Flow Scopes
(if_expression) @local.scope
(match_expression) @local.scope
(for_expression) @local.scope
(while_expression) @local.scope
(loop_expression) @local.scope

;; BDD Test Scopes
(feature_declaration) @local.scope
(scenario_declaration) @local.scope
(given_step) @local.scope
(when_step) @local.scope
(then_step) @local.scope
(and_then_step) @local.scope

;; Contract Scopes
(out_block) @local.scope
(out_err_block) @local.scope
(calc_block) @local.scope

;; Block Expressions
(block_expression) @local.scope

;; ============================================================================
;; Variable Definitions - Where variables are declared
;; ============================================================================

;; Modern Variable Declarations (val/var)
(val_declaration
  name: (identifier) @local.definition.var)

(var_declaration
  name: (identifier) @local.definition.var)

;; Legacy Variable Declarations (let)
(let_declaration
  name: (identifier) @local.definition.var)

;; Constants and Statics
(const_declaration
  name: (identifier) @local.definition.constant)

(static_declaration
  name: (identifier) @local.definition.constant)

;; Function Definitions
(function_declaration
  name: (identifier) @local.definition.function)

(method_declaration
  name: (identifier) @local.definition.method)

(static_method_declaration
  name: (identifier) @local.definition.method)

(mutable_method_declaration
  name: (identifier) @local.definition.method)

;; Type Definitions
(class_declaration
  name: (identifier) @local.definition.type)

(struct_declaration
  name: (identifier) @local.definition.type)

(enum_declaration
  name: (identifier) @local.definition.type)

(enum_variant
  name: (identifier) @local.definition.variant)

(union_declaration
  name: (identifier) @local.definition.type)

(trait_declaration
  name: (identifier) @local.definition.trait)

(mixin_declaration
  name: (identifier) @local.definition.mixin)

(actor_declaration
  name: (identifier) @local.definition.actor)

(unit_declaration
  name: (identifier) @local.definition.unit)

(type_alias
  name: (identifier) @local.definition.type)

;; Module Definitions
(module_declaration
  name: (identifier) @local.definition.namespace)

;; Mock Definitions
(mock_declaration
  name: (identifier) @local.definition.mock)

;; Parameters
(parameter
  name: (identifier) @local.definition.parameter)

(self_parameter) @local.definition.parameter

;; Lambda Parameters
(lambda_parameter
  name: (identifier) @local.definition.parameter)

;; Pattern Bindings (match, if let, etc.)
(pattern_binding
  name: (identifier) @local.definition.var)

(tuple_pattern
  (identifier) @local.definition.var)

(struct_pattern
  (field_pattern
    name: (identifier) @local.definition.var))

;; For Loop Variables
(for_expression
  variable: (identifier) @local.definition.var)

;; Field Definitions
(field_declaration
  name: (identifier) @local.definition.field)

;; BDD Step Variables
(given_step
  variable: (identifier) @local.definition.var)

(when_step
  variable: (identifier) @local.definition.var)

(then_step
  variable: (identifier) @local.definition.var)

;; Contract Quantifier Variables
(forall_expression
  variable: (identifier) @local.definition.var)

(exists_expression
  variable: (identifier) @local.definition.var)

;; Out/Out_err Bindings
(out_block
  name: (identifier) @local.definition.var)

(out_err_block
  name: (identifier) @local.definition.var)

;; ============================================================================
;; Variable References - Where variables are used
;; ============================================================================

;; All identifier references
(identifier) @local.reference

;; Member access (field references)
(member_expression
  property: (identifier) @local.reference)

;; Static access
(static_access
  member: (identifier) @local.reference)

;; ============================================================================
;; Shadowing Detection - Inner declarations that shadow outer ones
;; ============================================================================

;; Val/Var declarations that may shadow outer scope
(val_declaration
  name: (identifier) @local.shadow)

(var_declaration
  name: (identifier) @local.shadow)

;; Pattern bindings that shadow
(pattern_binding
  name: (identifier) @local.shadow)

;; For loop variables that shadow
(for_expression
  variable: (identifier) @local.shadow)

;; Lambda parameters that shadow
(lambda_parameter
  name: (identifier) @local.shadow)

;; Function parameters that shadow (less common but possible)
(parameter
  name: (identifier) @local.shadow)

;; Match case patterns that shadow
(match_arm
  pattern: (identifier) @local.shadow)

;; ============================================================================
;; Import/Export Tracking
;; ============================================================================

;; Module imports
(use_declaration
  path: (module_path) @local.import)

(import_declaration
  path: (module_path) @local.import)

;; Imported symbols
(use_item
  name: (identifier) @local.definition.imported)

;; Exported symbols
(export_declaration
  name: (identifier) @local.export)

;; ============================================================================
;; Generic Parameters (type variables)
;; ============================================================================

(type_parameter
  name: (identifier) @local.definition.type_parameter)

(type_parameter_list
  (identifier) @local.definition.type_parameter)

;; ============================================================================
;; Macro/Template Variables (if applicable)
;; ============================================================================

(macro_definition
  name: (identifier) @local.definition.macro)

(template_parameter
  name: (identifier) @local.definition.parameter)

;; ============================================================================
;; Special Variables
;; ============================================================================

;; self keyword
(self_parameter) @local.definition.builtin

;; Implicit self in methods
(member_expression
  object: (self) @local.reference.builtin)

;; ============================================================================
;; AOP Definitions
;; ============================================================================

;; Aspect definitions
(aspect_declaration
  name: (identifier) @local.definition.aspect)

;; Pointcut definitions
(pointcut_declaration
  name: (identifier) @local.definition.pointcut)

;; Advice definitions
(advice_declaration
  name: (identifier) @local.definition.advice)

;; Mock definitions
(mock_declaration
  name: (identifier) @local.definition.mock)

;; ============================================================================
;; Contract Variables
;; ============================================================================

;; Quantifier variables (forall/exists)
(quantifier_expression
  variable: (identifier) @local.definition.var)

;; Out block variables
(out_specification
  name: (identifier) @local.definition.var)

;; Calc block variables
(calc_expression
  variable: (identifier) @local.definition.var)

;; ============================================================================
;; BDD Variables
;; ============================================================================

;; Feature-level variables
(feature_declaration
  variable: (identifier) @local.definition.var)

;; Scenario-level variables
(scenario_declaration
  variable: (identifier) @local.definition.var)

;; Step variables
(step_variable
  name: (identifier) @local.definition.var)

;; Example table variables
(examples_table
  column: (identifier) @local.definition.var)

;; ============================================================================
;; Closure Captures
;; ============================================================================

;; Variables captured by lambdas/closures
(lambda_expression
  (identifier) @local.reference.captured)

(closure_expression
  (identifier) @local.reference.captured)

;; ============================================================================
;; Field Access Chains
;; ============================================================================

;; Chained member access
(member_expression
  object: (member_expression
    property: (identifier) @local.reference))

;; Optional chaining
(optional_chain
  property: (identifier) @local.reference)

;; ============================================================================
;; Type References in Expressions
;; ============================================================================

;; Type annotations
(type_annotation
  type: (type_identifier) @local.reference.type)

;; Type arguments in generics
(type_arguments
  (type_identifier) @local.reference.type)

;; Cast expressions
(cast_expression
  type: (type_identifier) @local.reference.type)

;; Constructor calls
(constructor_call
  type: (type_identifier) @local.reference.type)

;; ============================================================================
;; Special Scope Rules
;; ============================================================================

;; Match arms create new scopes for pattern variables
(match_arm) @local.scope

;; If-let creates scope for pattern variables
(if_let_expression) @local.scope

;; While-let creates scope for pattern variables
(while_let_expression) @local.scope

;; Try expressions create scope
(try_expression) @local.scope

;; Catch blocks create scope for error variable
(catch_clause
  variable: (identifier) @local.definition.var) @local.scope

;; ============================================================================
;; Lifetime Tracking (if applicable)
;; ============================================================================

;; Lifetime parameters
(lifetime_parameter
  name: (lifetime) @local.definition.lifetime)

;; Lifetime references
(lifetime) @local.reference.lifetime
