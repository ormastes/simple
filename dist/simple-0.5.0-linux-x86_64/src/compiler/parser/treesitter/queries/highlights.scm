;; highlights.scm - Syntax Highlighting for Simple Language
;; Tree-sitter query file for semantic token highlighting
;; Covers 100+ keywords, operators, literals, and language constructs

;; ============================================================================
;; Keywords - Core Language
;; ============================================================================

;; Variables and Constants
[
  "val"
  "var"
  "let"    ; legacy
  "const"
  "static"
] @keyword.variable

;; Functions and Methods
[
  "fn"
  "me"     ; mutable method
] @keyword.function

;; Types and Definitions
[
  "class"
  "struct"
  "enum"
  "union"
  "trait"
  "mixin"
  "impl"
  "type"
  "actor"
  "unit"
] @keyword.type

;; Module System
[
  "mod"
  "use"
  "import"
  "export"
  "common"
  "pub"
  "priv"
] @keyword.module

;; ============================================================================
;; Keywords - Control Flow
;; ============================================================================

;; Conditionals
[
  "if"
  "elif"
  "else"
  "match"
  "case"
] @keyword.control.conditional

;; Loops
[
  "for"
  "while"
  "loop"
  "break"
  "continue"
] @keyword.control.repeat

;; Returns and Jumps
[
  "return"
  "yield"
] @keyword.control.return

;; Exception Handling
[
  "try"
  "catch"
  "finally"
  "throw"
  "panic"
] @keyword.control.exception

;; ============================================================================
;; Keywords - Suspension/Async (if~, while~, and~, or~, etc.)
;; ============================================================================

[
  "if~"
  "while~"
  "and~"
  "or~"
  "not~"
  "match~"
  "for~"
] @keyword.control.suspension

;; Async/Await/Concurrency
[
  "async"
  "await"
  "spawn"
  "send"
  "receive"
] @keyword.control.async

;; ============================================================================
;; Keywords - Type System
;; ============================================================================

;; Type Modifiers
[
  "extends"
  "where"
  "self"
  "Self"
] @keyword.type.modifier

;; Capabilities
[
  "iso"    ; isolated
  "mut"    ; mutable
  "ref"    ; reference
  "val"    ; value (when used as capability)
  "dyn"    ; dynamic
] @keyword.capability

;; ============================================================================
;; Keywords - GPU/SIMD/Parallel
;; ============================================================================

[
  "vec"
  "shared"
  "gpu"
  "bounds"
  "kernel"
  "grid"
  "block"
  "simd"
] @keyword.gpu

;; ============================================================================
;; Keywords - AOP (Aspect-Oriented Programming)
;; ============================================================================

[
  "on"       ; advice binding
  "bind"     ; dependency injection
  "forbid"   ; architecture rule
  "allow"    ; architecture rule
  "mock"     ; mock definition
  "aspect"   ; aspect definition
] @keyword.aop

;; Pointcut keywords (inside pc{...})
[
  "call"
  "execution"
  "within"
  "args"
  "target"
  "this"
  "cflow"
] @keyword.aop.pointcut

;; ============================================================================
;; Keywords - Contracts
;; ============================================================================

[
  "requires"   ; precondition
  "ensures"    ; postcondition
  "invariant"  ; class invariant
  "out"        ; output specification
  "out_err"    ; error output specification
  "calc"       ; calculation proof
  "assert"     ; assertion
  "assume"     ; assumption
  "check"      ; runtime check
] @keyword.contract

;; Quantifiers
[
  "forall"
  "exists"
] @keyword.contract.quantifier

;; ============================================================================
;; Keywords - BDD/Testing
;; ============================================================================

[
  "feature"
  "scenario"
  "given"
  "when"
  "then"
  "and_then"
  "but"
  "examples"
  "it"
  "slow_it"
  "describe"
  "context"
] @keyword.test

;; ============================================================================
;; Operators
;; ============================================================================

;; Arithmetic
[
  "+"
  "-"
  "*"
  "/"
  "%"
  "**"     ; power
] @operator.arithmetic

;; Comparison
[
  "=="
  "!="
  "<"
  ">"
  "<="
  ">="
] @operator.comparison

;; Logical
[
  "and"
  "or"
  "not"
  "xor"
] @operator.logical

;; Bitwise
[
  "&"
  "|"
  "~"
  "<<"
  ">>"
] @operator.bitwise

;; Assignment
[
  "="
  "+="
  "-="
  "*="
  "/="
  "%="
  "&="
  "|="
  "^="
  "<<="
  ">>="
] @operator.assignment

;; Pipeline Operators
[
  "|>"     ; pipe forward
  ">>"     ; compose forward
  "<<"     ; compose backward
  "//"     ; parallel
  "~>"     ; layer connect (NN)
] @operator.pipeline

;; Dotted Operators (broadcasting)
[
  ".+"
  ".-"
  ".*"
  "./"
  ".^"
  ".%"
] @operator.broadcast

;; Matrix/Array
[
  "@"      ; matrix multiplication
] @operator.matrix

;; Optional/Nullable
[
  "?"      ; optional type suffix or try operator
  "??"     ; null coalescing
  "?."     ; optional chaining
  ".?"     ; existence check
] @operator.optional

;; Range
[
  ".."     ; exclusive range
  "..="    ; inclusive range
] @operator.range

;; Other
[
  "."      ; member access
  "::"     ; scope resolution
  ":"      ; type annotation
  "->"     ; return type
  "=>"     ; match arm
  "\\"     ; lambda (backslash)
  "|"      ; pipe lambda delimiters or closure
] @operator

;; ============================================================================
;; Literals
;; ============================================================================

;; Numbers
(integer_literal) @number
(float_literal) @number.float
(hex_literal) @number.hex
(binary_literal) @number.binary
(octal_literal) @number.octal

;; Strings
(string_literal) @string
(raw_string_literal) @string.raw
(char_literal) @string.char
(interpolated_string) @string.interpolated

;; String interpolation expressions
(interpolation) @embedded

;; Booleans
[
  "true"
  "false"
] @boolean

;; Null/None
[
  "nil"
  "None"
  "Some"
] @constant.builtin

;; Symbols
(symbol_literal) @symbol

;; ============================================================================
;; Comments
;; ============================================================================

(line_comment) @comment.line
(block_comment) @comment.block
(doc_comment) @comment.doc

;; ============================================================================
;; Functions and Methods
;; ============================================================================

;; Function Definitions
(function_declaration
  name: (identifier) @function)

(method_declaration
  name: (identifier) @method)

(mutable_method_declaration
  name: (identifier) @method.mutable)

(static_method_declaration
  name: (identifier) @method.static)

(lambda_expression) @function.lambda

;; Function Calls
(call_expression
  function: (identifier) @function.call)

(method_call_expression
  method: (identifier) @method.call)

(static_call_expression
  method: (identifier) @method.static.call)

;; ============================================================================
;; Types
;; ============================================================================

;; Type Definitions
(class_declaration
  name: (identifier) @type.class)

(struct_declaration
  name: (identifier) @type.struct)

(enum_declaration
  name: (identifier) @type.enum)

(union_declaration
  name: (identifier) @type.union)

(trait_declaration
  name: (identifier) @type.trait)

(actor_declaration
  name: (identifier) @type.actor)

(unit_declaration
  name: (identifier) @type.unit)

;; Type References
(type_identifier) @type

;; Generic Parameters
(type_parameter) @type.parameter
(type_argument) @type.argument

;; Built-in Types
[
  "i8" "i16" "i32" "i64" "i128"
  "u8" "u16" "u32" "u64" "u128"
  "f32" "f64"
  "bool"
  "text" "string"
  "char"
  "unit"
] @type.builtin

;; ============================================================================
;; Variables and Parameters
;; ============================================================================

;; Variable Declarations
(val_declaration
  name: (identifier) @variable.val)

(var_declaration
  name: (identifier) @variable.var)

(const_declaration
  name: (identifier) @constant)

(static_declaration
  name: (identifier) @constant.static)

;; Parameters
(parameter
  name: (identifier) @variable.parameter)

(self_parameter) @variable.builtin.self

;; Field Declarations
(field_declaration
  name: (identifier) @property)

;; Variable References
(identifier) @variable

;; ============================================================================
;; Modules and Imports
;; ============================================================================

(module_declaration
  name: (identifier) @namespace)

(use_declaration
  path: (module_path) @namespace.import)

(import_declaration
  path: (module_path) @namespace.import)

;; ============================================================================
;; Attributes and Annotations
;; ============================================================================

(attribute) @attribute
(decorator) @attribute.decorator

;; ============================================================================
;; Delimiters
;; ============================================================================

[
  "("
  ")"
  "["
  "]"
  "{"
  "}"
] @punctuation.bracket

[
  ","
  ";"
] @punctuation.delimiter

;; ============================================================================
;; Special Constructs
;; ============================================================================

;; Embedded Language Blocks
(sql_block) @embedded.sql
(sh_block) @embedded.shell
(html_block) @embedded.html
(re_block) @embedded.regex
(md_block) @embedded.markdown
(json_block) @embedded.json
(yaml_block) @embedded.yaml
(toml_block) @embedded.toml

;; Pointcut Expressions
(pointcut_expression) @embedded.pointcut

;; Math Blocks
(math_block) @embedded.math

;; ============================================================================
;; Errors (highlight known error patterns)
;; ============================================================================

(ERROR) @error
