; Tree-sitter Locals Queries for Simple Language
; Used for scope tracking, variable resolution, and semantic analysis

; ============================================================================
; Scopes - Define where new scopes begin
; ============================================================================

; Function scope
(function_declaration
  body: (_) @local.scope)

(function_def
  body: (_) @local.scope)

; Method scope
(method_declaration
  body: (_) @local.scope)

(method_def
  body: (_) @local.scope)

(static_method_def
  body: (_) @local.scope)

; Lambda/closure scope (all variants)
(lambda_expression
  body: (_) @local.scope)

(fn_lambda
  body: (_) @local.scope)

(backslash_lambda
  body: (_) @local.scope)

(pipe_lambda
  body: (_) @local.scope)

; Class scope
(class_declaration
  body: (_) @local.scope)

(class_def
  body: (_) @local.scope)

; Struct scope
(struct_def
  body: (_) @local.scope)

; Trait scope
(trait_declaration
  body: (_) @local.scope)

(trait_def
  body: (_) @local.scope)

; Mixin scope
(mixin_def
  body: (_) @local.scope)

; Impl block scope
(impl_block
  body: (_) @local.scope)

(impl_def
  body: (_) @local.scope)

; Actor scope
(actor_def
  body: (_) @local.scope)

; Module scope
(mod_def
  body: (_) @local.scope)

; Mock scope
(mock_def
  body: (_) @local.scope)

; Match arm scope
(match_arm
  body: (_) @local.scope)

(match_case
  body: (_) @local.scope)

; Block scope
(block) @local.scope

; For loop scope
(for_statement
  body: (_) @local.scope)

(for_stmt
  body: (_) @local.scope)

; While loop scope
(while_statement
  body: (_) @local.scope)

(while_stmt
  body: (_) @local.scope)

; Loop scope
(loop_stmt
  body: (_) @local.scope)

; If/else scope
(if_expression
  consequence: (_) @local.scope
  alternative: (_)? @local.scope)

(if_stmt
  body: (_) @local.scope)

; BDD scopes
(feature_def
  body: (_) @local.scope)

(scenario_def
  body: (_) @local.scope)

(given_step
  body: (_) @local.scope)

(when_step
  body: (_) @local.scope)

(then_step
  body: (_) @local.scope)

(and_then_step
  body: (_) @local.scope)

; Contract scopes
(out_stmt
  body: (_) @local.scope)

(out_err_stmt
  body: (_) @local.scope)

(calc_block
  body: (_) @local.scope)

; ============================================================================
; Definitions - Where variables/functions are defined
; ============================================================================

; Function definitions
(function_declaration
  name: (identifier) @local.definition.function)

(function_def
  name: (identifier) @local.definition.function)

; Method definitions
(method_declaration
  name: (identifier) @local.definition.method)

(method_def
  name: (identifier) @local.definition.method)

(static_method_def
  name: (identifier) @local.definition.method)

; Class definitions
(class_declaration
  name: (type_identifier) @local.definition.type)

(class_def
  name: (type_identifier) @local.definition.type)

; Struct definitions
(struct_def
  name: (type_identifier) @local.definition.type)

; Enum definitions
(enum_declaration
  name: (type_identifier) @local.definition.type)

(enum_def
  name: (type_identifier) @local.definition.type)

; Union definitions
(union_def
  name: (type_identifier) @local.definition.type)

; Trait definitions
(trait_declaration
  name: (type_identifier) @local.definition.type)

(trait_def
  name: (type_identifier) @local.definition.type)

; Mixin definitions
(mixin_def
  name: (type_identifier) @local.definition.type)

; Actor definitions
(actor_def
  name: (type_identifier) @local.definition.type)

; Type alias definitions
(type_alias
  name: (type_identifier) @local.definition.type)

(type_alias_stmt
  name: (type_identifier) @local.definition.type)

; Unit definitions
(unit_def
  name: (type_identifier) @local.definition.type)

; Handle pool definitions
(handle_pool_def
  type: (type_identifier) @local.definition.type)

; Mock definitions
(mock_def
  name: (type_identifier) @local.definition.type)

; Module definitions
(mod_def
  name: (identifier) @local.definition.namespace)

; Variable definitions (val/var bindings)
(val_stmt
  pattern: (identifier) @local.definition.var)

(var_stmt
  pattern: (identifier) @local.definition.var)

; Legacy let bindings
(let_statement
  pattern: (identifier) @local.definition.var)

(let_stmt
  pattern: (identifier) @local.definition.var)

; Const definitions
(const_stmt
  name: (identifier) @local.definition.constant)

; Static definitions
(static_stmt
  name: (identifier) @local.definition.var)

; Parameter definitions
(parameter
  (identifier) @local.definition.parameter)

; Pattern bindings in match
(pattern_binding
  (identifier) @local.definition.var)

; For loop variable
(for_statement
  pattern: (identifier) @local.definition.var)

(for_stmt
  pattern: (identifier) @local.definition.var)

; Field definitions
(field_declaration
  name: (identifier) @local.definition.field)

(field_def
  name: (identifier) @local.definition.field)

; BDD step pattern variables
(given_step
  pattern: (_) @local.definition.test)

(when_step
  pattern: (_) @local.definition.test)

(then_step
  pattern: (_) @local.definition.test)

; Contract quantifier variables
(forall_stmt
  variable: (identifier) @local.definition.var)

(exists_stmt
  variable: (identifier) @local.definition.var)

; Out/out_err bindings
(out_stmt
  result_binding: (identifier) @local.definition.var)

(out_err_stmt
  error_binding: (identifier) @local.definition.var)

; ============================================================================
; References - Where variables/functions are used
; ============================================================================

; Variable references (identifiers that are not definitions)
(identifier) @local.reference

; ============================================================================
; Imports - Bring external symbols into scope
; ============================================================================

; Import statement
(import_statement
  path: (module_path) @local.import)

; Specific imports
(import_item
  name: (identifier) @local.import.item)

; Import aliases
(import_alias
  alias: (identifier) @local.import.alias)

; ============================================================================
; Hoisting - Symbols visible before their definition
; ============================================================================

; Functions are hoisted (visible before definition)
(function_declaration
  name: (identifier) @local.hoist.function)

; Classes are hoisted
(class_declaration
  name: (type_identifier) @local.hoist.type)

; Enums are hoisted
(enum_declaration
  name: (type_identifier) @local.hoist.type)

; ============================================================================
; Shadowing - Track variable shadowing
; ============================================================================

; Inner val shadowing outer
(val_stmt
  pattern: (identifier) @local.shadow)

; Inner var shadowing outer
(var_stmt
  pattern: (identifier) @local.shadow)

; Inner let shadowing outer (legacy)
(let_statement
  pattern: (identifier) @local.shadow)

(let_stmt
  pattern: (identifier) @local.shadow)

; Pattern bindings can shadow
(pattern_binding
  (identifier) @local.shadow)

; For loop variables can shadow
(for_stmt
  pattern: (identifier) @local.shadow)

; Match case patterns can shadow
(match_case
  pattern: (identifier) @local.shadow)
