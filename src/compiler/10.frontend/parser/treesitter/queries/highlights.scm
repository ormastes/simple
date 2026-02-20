;; highlights.scm - Syntax Highlighting for Simple Language
;; Tree-sitter query file for semantic token highlighting
;; Covers 100+ keywords, operators, literals, and language constructs
;;
;; Keyword tiers: seed (bootstrap), core (self-hosting), full (runtime)
;; Aspirational keywords are marked with ;; aspirational
;; Source of truth: doc/spec/grammar/tier_keywords.sdn

;; ============================================================================
;; Keywords - Core Language
;; ============================================================================

;; Variables and Constants
[
  "val"       ; tier: seed
  "var"       ; tier: seed
  "let"       ; aspirational (legacy)
  "const"     ; tier: full
  "static"    ; tier: core
] @keyword.variable

;; Functions and Methods
[
  "fn"       ; tier: seed
  "me"       ; tier: core — mutable method
] @keyword.function

;; Types and Definitions
[
  "class"      ; tier: seed
  "struct"     ; tier: seed
  "enum"       ; tier: seed
  "union"      ; aspirational
  "trait"      ; tier: core
  "mixin"      ; aspirational
  "impl"       ; tier: seed
  "type"       ; tier: core
  "actor"      ; tier: full
  "unit"       ; tier: full
  "implements" ; tier: core
] @keyword.type

;; Module System
[
  "mod"        ; tier: full
  "use"        ; tier: seed
  "import"     ; tier: seed (deprecated)
  "export"     ; tier: seed
  "common"     ; aspirational
  "pub"        ; tier: core
  "priv"       ; aspirational (not a keyword, use pub for visibility)
] @keyword.module

;; ============================================================================
;; Keywords - Control Flow
;; ============================================================================

;; Conditionals
[
  "if"         ; tier: seed
  "elif"       ; tier: seed
  "else"       ; tier: seed
  "match"      ; tier: seed
  "case"       ; tier: seed
] @keyword.control.conditional

;; Loops
[
  "for"        ; tier: seed
  "while"      ; tier: seed
  "loop"       ; tier: core
  "break"      ; tier: seed
  "continue"   ; tier: seed
] @keyword.control.repeat

;; Returns and Jumps
[
  "return"     ; tier: seed
  "yield"      ; tier: core
] @keyword.control.return

;; Pass Variants (no-op placeholders)
[
  "pass"            ; tier: core
  "pass_todo"       ; tier: core
  "pass_do_nothing" ; tier: core
  "pass_dn"         ; tier: core
] @keyword.control

;; Exception Handling
[
  "try"        ; tier: full
  "catch"      ; tier: full
  "finally"    ; tier: full
  "throw"      ; tier: full
  "panic"      ; tier: full
] @keyword.control.exception

;; ============================================================================
;; Keywords - Suspension/Async (if~, while~, and~, or~, etc.)
;; ============================================================================

[
  "if~"        ; aspirational
  "while~"     ; aspirational
  "and~"       ; aspirational
  "or~"        ; aspirational
  "not~"       ; aspirational
  "match~"     ; aspirational
  "for~"       ; aspirational
] @keyword.control.suspension

;; Async/Await/Concurrency
[
  "async"      ; tier: core
  "await"      ; tier: core
  "spawn"      ; tier: core
  "send"       ; aspirational
  "receive"    ; aspirational
] @keyword.control.async

;; ============================================================================
;; Keywords - Type System
;; ============================================================================

;; Type Modifiers
[
  "extends"    ; aspirational
  "where"      ; aspirational
  "self"       ; tier: core
  "Self"       ; aspirational
] @keyword.type.modifier

;; Capabilities
[
  "iso"        ; aspirational — isolated
  "mut"        ; aspirational — mutable
  "ref"        ; aspirational — reference
  "val"        ; tier: seed (also used as capability)
  "dyn"        ; aspirational — dynamic
] @keyword.capability

;; ============================================================================
;; Keywords - GPU/SIMD/Parallel
;; ============================================================================

[
  "vec"        ; aspirational
  "shared"     ; tier: full
  "gpu"        ; aspirational
  "bounds"     ; aspirational
  "kernel"     ; tier: full
  "grid"       ; aspirational
  "block"      ; aspirational
  "simd"       ; aspirational
] @keyword.gpu

;; ============================================================================
;; Keywords - AOP (Aspect-Oriented Programming) — all aspirational
;; ============================================================================

[
  "on"       ; aspirational — advice binding
  "bind"     ; aspirational — dependency injection
  "forbid"   ; aspirational — architecture rule
  "allow"    ; aspirational — architecture rule
  "mock"     ; aspirational — mock definition
  "aspect"   ; aspirational — aspect definition
] @keyword.aop

;; Pointcut keywords (inside pc{...}) — all aspirational
[
  "call"       ; aspirational
  "execution"  ; aspirational
  "within"     ; aspirational
  "args"       ; aspirational
  "target"     ; aspirational
  "this"       ; aspirational
  "cflow"      ; aspirational
] @keyword.aop.pointcut

;; ============================================================================
;; Keywords - Contracts — all aspirational
;; ============================================================================

[
  "requires"   ; aspirational — precondition
  "ensures"    ; aspirational — postcondition
  "invariant"  ; aspirational — class invariant
  "out"        ; aspirational — output specification
  "out_err"    ; aspirational — error output specification
  "calc"       ; aspirational — calculation proof
  "assert"     ; aspirational — assertion (reserved keyword in runtime)
  "assume"     ; aspirational — assumption
  "check"      ; aspirational — runtime check
] @keyword.contract

;; Quantifiers — aspirational
[
  "forall"     ; aspirational
  "exists"     ; aspirational
] @keyword.contract.quantifier

;; ============================================================================
;; Keywords - BDD/Testing — built-in to runtime (not parser keywords)
;; ============================================================================

[
  "feature"    ; aspirational
  "scenario"   ; aspirational
  "given"      ; aspirational
  "when"       ; aspirational
  "then"       ; aspirational
  "and_then"   ; aspirational
  "but"        ; aspirational
  "examples"   ; aspirational
  "it"         ; built-in function (not keyword)
  "slow_it"    ; built-in function (not keyword)
  "describe"   ; built-in function (not keyword)
  "context"    ; built-in function (not keyword)
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
