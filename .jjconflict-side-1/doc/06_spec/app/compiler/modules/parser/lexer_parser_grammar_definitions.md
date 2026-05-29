# Simple Language Grammar - Part 1: Definitions

Part of [Simple Language Grammar](lexer_parser_grammar.md).

## Tree-sitter Grammar - Definitions (`grammar.js`)

```javascript
// grammar.js - Complete Tree-sitter grammar for Simple language
// Uses GLR parsing for ambiguity resolution
// Part 1: Definitions (types, structs, classes, enums, traits, modules)

module.exports = grammar({
  name: 'simple',

  // External scanner handles indentation
  externals: $ => [
    $._indent,
    $._dedent,
    $._newline,
    $._string_start,
    $._string_content,
    $._string_end,
  ],

  // Token precedence for GLR conflict resolution
  precedences: $ => [
    [
      'call',
      'unary',
      'power',
      'multiplicative',
      'additive',
      'shift',
      'bitwise_and',
      'bitwise_xor',
      'bitwise_or',
      'comparison',
      'logical_and',
      'logical_or',
      'functional_update',
      'assignment',
    ],
    ['type_args', 'comparison'],
    ['primary', 'lambda'],
  ],

  // Inline rules for performance
  inline: $ => [
    $._statement,
    $._simple_statement,
    $._compound_statement,
    $._expression,
  ],

  // Conflict resolution for GLR parsing
  conflicts: $ => [
    // Type vs expression ambiguity
    [$.type, $.primary_expression],
    // Generic type vs comparison
    [$.generic_type, $.comparison_expression],
    // Lambda vs block
    [$.lambda_expression, $.block],
    // Pattern vs expression
    [$.pattern, $.primary_expression],
    // Struct literal vs block
    [$.struct_literal, $.block],
  ],

  // Word token for keyword extraction
  word: $ => $.identifier,

  rules: {
    //=========================================================================
    // SOURCE FILE
    //=========================================================================

    source_file: $ => repeat($._definition),

    _definition: $ => choice(
      $.decorated_definition,
      $.attributed_definition,
      $.function_definition,
      $.struct_definition,
      $.class_definition,
      $.enum_definition,
      $.trait_definition,
      $.impl_block,
      $.actor_definition,
      $.handle_pool_definition,
      $.macro_definition,
      $.global_declaration,
      $.type_alias,
      $.unit_family,
      $.unit_standalone,
      // Module system
      $.module_declaration,
      $.use_statement,
      $.common_use_statement,
      $.export_use_statement,
      $.auto_import_statement,
      // AOP and testing
      $.bitfield_definition,
      $.aop_advice,
      $.mock_declaration,
      $.di_binding,
      $.architecture_rule,
    ),

    //=========================================================================
    // DECORATORS AND ATTRIBUTES
    //=========================================================================

    // @decorator syntax (function transformers)
    decorated_definition: $ => seq(
      repeat1($.decorator),
      choice(
        $.function_definition,
        $.class_definition,
        $.method_definition,
      ),
    ),

    decorator: $ => seq(
      '@',
      $.identifier,
      optional(seq('(', commaSep($.argument), ')')),
      $._newline,
    ),

    // #[attribute] syntax (metadata)
    attributed_definition: $ => seq(
      repeat1($.attribute),
      $._definition,
    ),

    attribute: $ => seq(
      '#',
      '[',
      $.identifier,
      optional(seq('(', commaSep($.attribute_argument), ')')),
      ']',
      $._newline,
    ),

    attribute_argument: $ => choice(
      $.identifier,
      $.literal,
      seq($.identifier, ':', $.expression),
    ),

    // Built-in attributes:
    // - #[inline]           - Hint to inline function
    // - #[deprecated]       - Mark as deprecated
    // - #[derive(...)]      - Auto-derive trait implementations
    // - #[strong]           - Enum: disallow wildcard _ in pattern matching
    // - #[allow(wildcard)]  - Match case: opt-out of strong enum check
    // - #[warn_primitive]   - Enable primitive API warnings
    // - #[allow_primitive]  - Suppress primitive API warning

    //=========================================================================
    // TYPE SYSTEM
    //=========================================================================

    type: $ => choice(
      $.simple_type,
      $.generic_type,
      $.pointer_type,
      $.tuple_type,
      $.array_type,
      $.dict_type,
      $.function_type,
      $.union_type,
      $.optional_type,
      $.constructor_type,
    ),

    simple_type: $ => $.type_identifier,

    type_identifier: $ => /[A-Z][a-zA-Z0-9_]*/,

    generic_type: $ => prec('type_args', seq(
      $.type_identifier,
      '<',
      commaSep1($.type),
      '>',
    )),

    // Pointer types: &T (unique), *T (shared), -T (weak), +T (handle)
    pointer_type: $ => choice(
      seq('&', $.type),      // Unique pointer
      seq('*', $.type),      // Shared pointer
      seq('-', $.type),      // Weak pointer
      seq('+', $.type),      // Handle pointer
    ),

    tuple_type: $ => seq(
      '(',
      commaSep($.type),
      ')',
    ),

    array_type: $ => seq(
      '[',
      $.type,
      optional(seq(';', $.expression)),  // Fixed-size array
      ']',
    ),

    dict_type: $ => seq(
      '{',
      $.type,
      ':',
      $.type,
      '}',
    ),

    function_type: $ => seq(
      'Fn',
      '(',
      commaSep($.type),
      ')',
      optional(seq('->', $.type)),
    ),

    union_type: $ => prec.left(seq(
      $.type,
      '|',
      $.type,
    )),

    optional_type: $ => seq(
      $.type,
      '?',
    ),

    // Constructor type for factory patterns: Constructor<T>
    // Represents a callable that creates instances of T
    constructor_type: $ => seq(
      'Constructor',
      '<',
      $.type,
      '>',
    ),

    type_parameters: $ => seq(
      '<',
      commaSep1($.type_parameter),
      '>',
    ),

    type_parameter: $ => seq(
      $.identifier,
      optional(seq(':', $.type_bounds)),
    ),

    type_bounds: $ => sep1($.type, '+'),

    //=========================================================================
    // STRUCT DEFINITION
    //=========================================================================

    struct_definition: $ => seq(
      optional('mut'),
      'struct',
      $.type_identifier,
      optional($.type_parameters),
      ':',
      $._indent,
      repeat1($.field_definition),
      $._dedent,
    ),

    field_definition: $ => seq(
      $.identifier,
      ':',
      $.type,
      optional(seq('=', $.expression)),
      $._newline,
    ),

    //=========================================================================
    // CLASS DEFINITION
    //=========================================================================

    class_definition: $ => seq(
      optional('immut'),
      'class',
      $.type_identifier,
      optional($.type_parameters),
      optional($.superclass),
      ':',
      $._indent,
      repeat(choice(
        $.field_definition,
        $.method_definition,
      )),
      $._dedent,
    ),

    superclass: $ => seq(
      '(',
      $.type,
      ')',
    ),

    // Method definition with optional 'me' for mutable methods
    // - 'fn name()' = immutable method (implicit self)
    // - 'me name()' = mutable method (implicit mutable self)
    // - 'static fn name()' = static method (no self)
    method_definition: $ => seq(
      optional('pub'),
      choice(
        seq(optional('static'), 'fn'),  // Immutable or static method
        'me',                            // Mutable method
      ),
      $.identifier,
      $.parameters,
      optional($.effect_modifier),
      optional(seq('->', $.type)),
      ':',
      $.block,
    ),

    //=========================================================================
    // ENUM DEFINITION
    //=========================================================================

    enum_definition: $ => seq(
      'enum',
      $.type_identifier,
      optional($.type_parameters),
      ':',
      $._indent,
      repeat1($.enum_variant),
      $._dedent,
    ),

    enum_variant: $ => seq(
      $.type_identifier,
      optional($.variant_fields),
      $._newline,
    ),

    variant_fields: $ => seq(
      '(',
      commaSep($.variant_field),
      ')',
    ),

    variant_field: $ => seq(
      optional(seq($.identifier, ':')),
      $.type,
    ),

    //=========================================================================
    // TRAIT DEFINITION
    //=========================================================================

    trait_definition: $ => seq(
      'trait',
      $.type_identifier,
      optional($.type_parameters),
      optional($.trait_bounds),
      ':',
      $._indent,
      repeat($.trait_method),
      $._dedent,
    ),

    trait_bounds: $ => seq(
      '(',
      commaSep1($.type),
      ')',
    ),

    trait_method: $ => seq(
      'fn',
      $.identifier,
      $.parameters,
      optional($.effect_modifier),
      optional(seq('->', $.type)),
      optional(seq(':', $.block)),
      $._newline,
    ),

    //=========================================================================
    // IMPL BLOCK
    //=========================================================================

    impl_block: $ => seq(
      'impl',
      optional($.type_parameters),
      $.type,
      optional(seq('for', $.type)),
      ':',
      $._indent,
      repeat($.method_definition),
      $._dedent,
    ),

    //=========================================================================
    // ACTOR DEFINITION
    //=========================================================================

    actor_definition: $ => seq(
      'actor',
      $.type_identifier,
      optional($.type_parameters),
      ':',
      $._indent,
      optional($.state_block),
      repeat($.message_handler),
      $._dedent,
    ),

    state_block: $ => seq(
      'state',
      ':',
      $._indent,
      repeat1($.field_definition),
      $._dedent,
    ),

    message_handler: $ => seq(
      'on',
      $.type_identifier,
      optional($.handler_parameters),
      $.effect_modifier,  // must be 'async' for stackless actors
      ':',
      $.block,
    ),

    handler_parameters: $ => seq(
      '(',
      commaSep($.parameter),
      ')',
    ),

    //=========================================================================
    // HANDLE POOL DEFINITION
    //=========================================================================

    handle_pool_definition: $ => seq(
      'handle_pool',
      $.type_identifier,
      ':',
      $._indent,
      repeat1($.pool_option),
      $._dedent,
    ),

    pool_option: $ => seq(
      $.identifier,
      ':',
      $.expression,
      $._newline,
    ),

    //=========================================================================
    // FUNCTION DEFINITION
    //=========================================================================

    function_definition: $ => seq(
      optional($.visibility),
      optional('extern'),
      'fn',
      $.identifier,
      optional($.type_parameters),
      $.parameters,
      optional($.effect_modifier),
      optional(seq('->', $.type)),
      ':',
      $.block,
    ),

    visibility: $ => choice('pub', 'priv'),

    parameters: $ => seq(
      '(',
      commaSep($.parameter),
      ')',
    ),

    parameter: $ => seq(
      optional('mut'),
      $.identifier,
      optional(seq(':', $.type)),
      optional(seq('=', $.expression)),
    ),

    effect_modifier: $ => 'async',

    //=========================================================================
    // MACRO DEFINITION
    //=========================================================================

    macro_definition: $ => seq(
      'macro',
      $.identifier,
      $.macro_parameters,
      ':',
      $._indent,
      $.macro_body,
      $._dedent,
    ),

    macro_parameters: $ => seq(
      '(',
      commaSep($.macro_parameter),
      ')',
    ),

    macro_parameter: $ => seq(
      $.identifier,
      ':',
      $.macro_type,
    ),

    macro_type: $ => choice(
      'Ident',
      'Type',
      'Expr',
      'Block',
      'Pattern',
      seq('[', $.macro_type, ']'),
    ),

    macro_body: $ => seq(
      'gen_code',
      ':',
      $._indent,
      repeat($._statement),
      $._dedent,
    ),

    //=========================================================================
    // GLOBAL DECLARATIONS
    //=========================================================================

    global_declaration: $ => choice(
      $.const_declaration,
      $.static_declaration,
    ),

    const_declaration: $ => seq(
      'const',
      $.identifier,
      optional(seq(':', $.type)),
      '=',
      $.expression,
      $._newline,
    ),

    static_declaration: $ => seq(
      optional('mut'),
      'static',
      $.identifier,
      ':',
      $.type,
      '=',
      $.expression,
      $._newline,
    ),

    type_alias: $ => seq(
      'type',
      $.type_identifier,
      optional($.type_parameters),
      '=',
      $.type,
      $._newline,
    ),

    //=========================================================================
    // MODULE SYSTEM
    //=========================================================================

    // Module declaration: mod name or pub mod name
    // Used in __init__.spl for directory manifest
    module_declaration: $ => seq(
      optional($.visibility),
      optional(repeat($.attribute)),
      'mod',
      $.identifier,
      $._newline,
    ),

    // Module path: crate.sys.http or sys.http.router
    module_path: $ => sep1($.identifier, '.'),

    // Import path item: single name, glob (*), or group ({A, B})
    import_item: $ => choice(
      $.identifier,                           // Single name
      '*',                                    // Glob import
      seq('{', commaSep1($.identifier), '}'), // Group import
    ),

    // Normal import: use crate.sys.http.Router
    use_statement: $ => seq(
      'use',
      $.module_path,
      optional(seq('.', $.import_item)),
      $._newline,
    ),

    // Directory prelude: common use crate.core.base.*
    common_use_statement: $ => seq(
      'common',
      'use',
      $.module_path,
      optional(seq('.', $.import_item)),
      $._newline,
    ),

    // Public re-export: export use router.Router
    export_use_statement: $ => seq(
      'export',
      'use',
      $.module_path,
      optional(seq('.', $.import_item)),
      $._newline,
    ),

    // Macro auto-import (one per line): auto import router.route
    auto_import_statement: $ => seq(
      'auto',
      'import',
      $.module_path,
      '.',
      $.identifier,
      $._newline,
    ),

    //=========================================================================
    // UNIT TYPES
    //=========================================================================

    // Unit family: unit length(base: f64): m = 1.0, km = 1000.0
    unit_family: $ => seq(
      'unit',
      $.identifier,                    // length
      '(',
      'base',
      ':',
      $.type,                          // f64
      ')',
      optional($.unit_composite_clause),
      ':',
      $._indent,
      repeat1($.unit_suffix_def),
      $._dedent,
    ),

    // Composite clause: = length / time
    unit_composite_clause: $ => seq(
      '=',
      $.type_identifier,               // length
      $.unit_operator,                 // /, *, ^
      choice($.type_identifier, $.integer, $.float),  // time or 3
    ),

    unit_operator: $ => choice('/', '*', '^'),

    // Suffix definition: km = 1000.0
    unit_suffix_def: $ => seq(
      $.identifier,                    // km
      '=',
      choice($.integer, $.float),      // 1000.0
      $._newline,
    ),

    // Standalone unit: unit UserId: i64 as uid [= factor]
    unit_standalone: $ => seq(
      'unit',
      $.type_identifier,               // UserId
      ':',
      $.type,                          // i64
      'as',
      $.identifier,                    // uid (suffix)
      optional(seq('=', $.expression)), // = 0.01
      $._newline,
    ),

    // Suffixed literal: 100_km, 5.5_hr, 42_uid
    suffixed_literal: $ => seq(
      choice($.integer, $.float),      // 100
      '_',
      $.identifier,                    // km
    ),

    //=========================================================================
    // BITFIELD DEFINITION
    //=========================================================================

    // Bitfield: compact binary representation with bit-level field packing
    // Example: bitfield Flags(u32): active: 1, mode: 3, _reserved: 4
    bitfield_definition: $ => seq(
      optional($.visibility),
      'bitfield',
      $.type_identifier,
      optional(seq('(', $.type, ')')),  // Base storage type
      ':',
      $._indent,
      repeat1($.bitfield_field),
      repeat($.bitfield_constant),
      $._dedent,
    ),

    bitfield_field: $ => seq(
      $.identifier,                     // Field name (or _reserved)
      ':',
      choice(
        $.integer,                      // Bit width: 1, 3, 8
        $.unit_with_repr,               // Unit with repr: cm:i12
      ),
      $._newline,
    ),

    // Unit type with representation constraint: cm:i12 (12-bit signed centimeters)
    unit_with_repr: $ => seq(
      $.identifier,                     // Unit suffix: cm, ms
      ':',
      $.repr_type,                      // Representation: i12, u8
    ),

    repr_type: $ => /[iu]\d+|f32|f64/,  // i12, u8, f32, etc.

    bitfield_constant: $ => seq(
      'const',
      $.identifier,
      '=',
      $.expression,
      $._newline,
    ),

    //=========================================================================
    // AOP (ASPECT-ORIENTED PROGRAMMING)
    //=========================================================================

    // Predicate expression within pc{...} syntactic island
    // Supports boolean combinators and selector functions
    predicate_expr: $ => choice(
      $.predicate_selector,
      $.predicate_not,
      $.predicate_and,
      $.predicate_or,
    ),

    predicate_selector: $ => seq(
      $.identifier,                     // Selector name: execution, call, within
      '(',
      commaSep($.pattern_string),       // Pattern arguments
      ')',
    ),

    pattern_string: $ => /[^,()]+/,     // Pattern string (e.g., "* User.new(..)")

    predicate_not: $ => seq('!', $.predicate_expr),

    predicate_and: $ => prec.left(seq(
      $.predicate_expr,
      '&',
      $.predicate_expr,
    )),

    predicate_or: $ => prec.left(seq(
      $.predicate_expr,
      '|',
      $.predicate_expr,
    )),

    // Pointcut block: pc{...}
    pointcut: $ => seq(
      'pc',
      '{',
      $.predicate_expr,
      '}',
    ),

    // AOP advice declaration: on pc{...} use <Interceptor>
    // Advice types: before, after_success, after_error, around
    aop_advice: $ => seq(
      'on',
      $.pointcut,
      optional($.advice_type),
      'use',
      $.module_path,                    // Interceptor class/function
      optional(seq('priority', $.integer)),
      $._newline,
    ),

    advice_type: $ => choice(
      'before',
      'after_success',
      'after_error',
      'around',
    ),

    // DI binding: bind on pc{...} -> <Impl> [scope] [priority]
    di_binding: $ => seq(
      'bind',
      'on',
      $.pointcut,
      '->',
      $.module_path,                    // Implementation type
      optional($.di_scope),
      optional(seq('priority', $.integer)),
      $._newline,
    ),

    di_scope: $ => choice(
      'singleton',
      'transient',
      'scoped',
    ),

    // Architecture rule: forbid/allow pc{...}
    architecture_rule: $ => seq(
      choice('forbid', 'allow'),
      $.pointcut,
      optional($.string),               // Optional message
      $._newline,
    ),

    //=========================================================================
    // MOCK DECLARATION (Testing)
    //=========================================================================

    // Mock declaration: mock Name implements Trait:
    mock_declaration: $ => seq(
      'mock',
      $.type_identifier,
      'implements',
      $.type,                           // Trait being mocked
      ':',
      $._indent,
      repeat($.mock_expectation),
      $._dedent,
    ),

    // Mock expectation: expect method() -> Type:
    mock_expectation: $ => seq(
      'expect',
      $.identifier,
      $.parameters,
      optional(seq('->', $.type)),
      ':',
      $.block,
    ),

    // ... continued in Part 2: Statements & Expressions
  },
});

// Helper functions
function commaSep(rule) {
  return optional(commaSep1(rule));
}

function commaSep1(rule) {
  return seq(rule, repeat(seq(',', rule)), optional(','));
}

function sep1(rule, separator) {
  return seq(rule, repeat(seq(separator, rule)));
}
```

---

Next: [Part 2: Statements & Expressions](lexer_parser_grammar_expressions.md) | Back to: [Grammar Index](lexer_parser_grammar.md)
