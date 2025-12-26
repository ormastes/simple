; Tree-sitter Highlight Queries for Simple Language
; Used by LSP semantic tokens provider

; ============================================================================
; Keywords - Highest Priority
; ============================================================================

; Core keywords
[
  "fn"
  "let"
  "class"
  "enum"
  "trait"
  "impl"
  "type"
  "import"
  "export"
  "from"
  "as"
  "pub"
] @keyword

; Control flow
[
  "if"
  "else"
  "elif"
  "match"
  "case"
  "for"
  "while"
  "loop"
  "break"
  "continue"
  "return"
] @keyword.control

; Async/concurrency
[
  "async"
  "await"
  "actor"
  "spawn"
  "send"
  "recv"
  "yield"
] @keyword.async

; Effects
[
  "effect"
  "io"
  "file"
  "net"
  "unsafe"
] @keyword.effect

; Memory modifiers
[
  "mut"
  "iso"
  "ref"
  "move"
] @keyword.modifier

; ============================================================================
; Functions - High Priority
; ============================================================================

; Function definitions
(function_declaration
  name: (identifier) @function.definition
  (#set! "priority" 100))

; Method definitions
(method_declaration
  name: (identifier) @function.method.definition
  (#set! "priority" 100))

; Constructor definitions
(constructor_declaration
  name: (identifier) @function.constructor
  (#set! "priority" 100))

; Function calls
(call_expression
  function: (identifier) @function.call)

; Method calls
(method_call_expression
  method: (identifier) @function.method.call)

; Builtin functions
((identifier) @function.builtin
  (#match? @function.builtin "^(print|println|panic|assert|len|range|enumerate)$"))

; ============================================================================
; Types
; ============================================================================

; Type identifiers
(type_identifier) @type

; Primitive types
[
  "i8" "i16" "i32" "i64" "i128"
  "u8" "u16" "u32" "u64" "u128"
  "f32" "f64"
  "bool"
  "String"
  "char"
  "void"
  "never"
] @type.builtin

; Type parameters (generics)
(type_parameters
  (type_identifier) @type.parameter)

; Type constraints
(type_constraint
  (type_identifier) @type.parameter)

; Class declarations
(class_declaration
  name: (type_identifier) @type.class.definition
  (#set! "priority" 101))

; Enum declarations
(enum_declaration
  name: (type_identifier) @type.enum.definition
  (#set! "priority" 101))

; Trait declarations
(trait_declaration
  name: (type_identifier) @type.trait.definition
  (#set! "priority" 101))

; Enum variants
(enum_variant
  name: (identifier) @type.variant)

; ============================================================================
; Variables and Parameters
; ============================================================================

; Parameters (higher priority than variables)
(parameter
  (identifier) @parameter
  (#set! "priority" 101))

; Self parameter
(self_parameter) @variable.builtin

; Let bindings
(let_statement
  pattern: (identifier) @variable.definition)

; Pattern bindings in match
(pattern_binding
  (identifier) @variable.definition)

; Variable references
(identifier) @variable

; ============================================================================
; Fields and Properties
; ============================================================================

; Field declarations
(field_declaration
  name: (identifier) @property.definition)

; Field access
(field_access
  field: (identifier) @property)

; Struct field in literal
(struct_field
  name: (identifier) @property)

; ============================================================================
; Literals
; ============================================================================

; Numbers
(integer_literal) @number
(float_literal) @number
(hex_literal) @number
(binary_literal) @number
(octal_literal) @number

; Strings
(string_literal) @string
(raw_string_literal) @string.special
(byte_string_literal) @string.special

; F-strings
(fstring_literal) @string.special
(fstring_expression) @embedded

; Characters
(char_literal) @character

; Booleans
[
  "true"
  "false"
] @boolean

; None/nil
[
  "none"
  "nil"
  "None"
] @constant.builtin

; ============================================================================
; Operators
; ============================================================================

; Arithmetic
[
  "+"
  "-"
  "*"
  "/"
  "%"
  "**"
] @operator.arithmetic

; Comparison
[
  "=="
  "!="
  "<"
  ">"
  "<="
  ">="
] @operator.comparison

; Logical
[
  "and"
  "or"
  "not"
  "&&"
  "||"
  "!"
] @operator.logical

; Bitwise
[
  "&"
  "|"
  "^"
  "<<"
  ">>"
  "~"
] @operator.bitwise

; Assignment
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

; Special operators
[
  "?"
  "??"
  "?."
  "!!"
  ".."
  "..="
  "=>"
  "->"
  "::"
  "@"
] @operator.special

; ============================================================================
; Punctuation
; ============================================================================

; Brackets
["(" ")"] @punctuation.bracket
["[" "]"] @punctuation.bracket
["{" "}"] @punctuation.bracket

; Delimiters
["," ";"] @punctuation.delimiter
[":" "." "->"] @punctuation.delimiter

; ============================================================================
; Comments
; ============================================================================

; Line comments
(line_comment) @comment

; Block comments
(block_comment) @comment

; Doc comments (special highlighting)
(doc_comment) @comment.documentation

; TODO/FIXME/NOTE in comments
((comment) @comment.todo
  (#match? @comment.todo "TODO|FIXME|XXX|HACK|NOTE"))

; ============================================================================
; Attributes and Decorators
; ============================================================================

; Decorators
(decorator
  "@" @punctuation.special
  name: (identifier) @function.decorator)

; Attributes
(attribute
  "#[" @punctuation.special
  name: (identifier) @attribute
  "]" @punctuation.special)

; ============================================================================
; Modules and Imports
; ============================================================================

; Module paths
(module_path
  (identifier) @namespace)

; Import paths
(import_path
  (identifier) @namespace)

; ============================================================================
; Special Constructs
; ============================================================================

; Contract keywords
[
  "in"
  "out"
  "invariant"
  "old"
  "ensures"
  "requires"
] @keyword.contract

; Labels
(label
  (identifier) @label)

; Escape sequences in strings
(escape_sequence) @string.escape

; Format specifiers in f-strings
(format_specifier) @string.special

; ============================================================================
; Errors (if tree-sitter reports them)
; ============================================================================

(ERROR) @error
