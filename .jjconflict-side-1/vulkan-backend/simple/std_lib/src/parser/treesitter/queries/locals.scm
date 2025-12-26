; Tree-sitter Locals Queries for Simple Language
; Used for scope tracking, variable resolution, and semantic analysis

; ============================================================================
; Scopes - Define where new scopes begin
; ============================================================================

; Function scope
(function_declaration
  body: (_) @local.scope)

; Method scope
(method_declaration
  body: (_) @local.scope)

; Lambda/closure scope
(lambda_expression
  body: (_) @local.scope)

; Class scope
(class_declaration
  body: (_) @local.scope)

; Trait scope
(trait_declaration
  body: (_) @local.scope)

; Impl block scope
(impl_block
  body: (_) @local.scope)

; Match arm scope
(match_arm
  body: (_) @local.scope)

; Block scope
(block) @local.scope

; For loop scope
(for_statement
  body: (_) @local.scope)

; While loop scope
(while_statement
  body: (_) @local.scope)

; If/else scope
(if_expression
  consequence: (_) @local.scope
  alternative: (_)? @local.scope)

; ============================================================================
; Definitions - Where variables/functions are defined
; ============================================================================

; Function definitions
(function_declaration
  name: (identifier) @local.definition.function)

; Method definitions
(method_declaration
  name: (identifier) @local.definition.method)

; Class definitions
(class_declaration
  name: (type_identifier) @local.definition.type)

; Enum definitions
(enum_declaration
  name: (type_identifier) @local.definition.type)

; Trait definitions
(trait_declaration
  name: (type_identifier) @local.definition.type)

; Type alias definitions
(type_alias
  name: (type_identifier) @local.definition.type)

; Variable definitions (let bindings)
(let_statement
  pattern: (identifier) @local.definition.var)

; Parameter definitions
(parameter
  (identifier) @local.definition.parameter)

; Pattern bindings in match
(pattern_binding
  (identifier) @local.definition.var)

; For loop variable
(for_statement
  pattern: (identifier) @local.definition.var)

; Field definitions
(field_declaration
  name: (identifier) @local.definition.field)

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

; Inner let shadowing outer
(let_statement
  pattern: (identifier) @local.shadow)
