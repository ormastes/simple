# Simple Language Grammar - Part 2: Statements & Expressions

Part of [Simple Language Grammar](lexer_parser_grammar.md).

## Tree-sitter Grammar - Statements & Expressions (`grammar.js`)

```javascript
// grammar.js - Complete Tree-sitter grammar for Simple language
// Part 2: Statements, Patterns, Expressions (continued from Part 1)

  rules: {
    // ... continued from Part 1: Definitions

    //=========================================================================
    // STATEMENTS
    //=========================================================================

    block: $ => seq(
      $._indent,
      repeat1($._statement),
      $._dedent,
    ),

    _statement: $ => choice(
      $._simple_statement,
      $._compound_statement,
    ),

    _simple_statement: $ => seq(
      choice(
        $.expression_statement,
        $.assignment_statement,
        $.val_statement,          // val name = value (immutable, preferred)
        $.var_statement,          // var name = value (mutable)
        $.let_statement,          // let name = value (alternative)
        $.return_statement,
        $.break_statement,
        $.continue_statement,
        $.pass_statement,
        $.send_statement,
      ),
      $._newline,
    ),

    _compound_statement: $ => choice(
      $.if_statement,
      $.if_let_statement,
      $.match_statement,
      $.for_statement,
      $.while_statement,
      $.while_let_statement,
      $.loop_statement,
      $.with_statement,
      $.receive_block,
      $.context_block,
    ),

    expression_statement: $ => $.expression,

    assignment_statement: $ => seq(
      $.expression,
      '=',
      $.expression,
    ),

    // Variable declarations (Scala-style preferred)
    // val name = value   # Immutable (preferred)
    // var name = value   # Mutable
    // let name = value   # Alternative immutable syntax
    val_statement: $ => seq(
      'val',
      $.pattern,
      optional(seq(':', $.type)),
      '=',
      $.expression,
    ),

    var_statement: $ => seq(
      'var',
      $.pattern,
      optional(seq(':', $.type)),
      '=',
      $.expression,
    ),

    let_statement: $ => seq(
      optional('mut'),
      'let',
      $.pattern,
      optional(seq(':', $.type)),
      optional(seq('=', $.expression)),
    ),

    return_statement: $ => seq(
      'return',
      optional($.expression),
    ),

    break_statement: $ => seq(
      'break',
      optional($.identifier),
    ),

    continue_statement: $ => seq(
      'continue',
      optional($.identifier),
    ),

    pass_statement: $ => 'pass',

    send_statement: $ => seq(
      'send',
      $.expression,
      ',',
      $.expression,
    ),

    //=========================================================================
    // COMPOUND STATEMENTS
    //=========================================================================

    if_statement: $ => seq(
      'if',
      $.expression,
      ':',
      $.block,
      repeat($.elif_clause),
      optional($.else_clause),
    ),

    elif_clause: $ => seq(
      'elif',
      $.expression,
      ':',
      $.block,
    ),

    else_clause: $ => seq(
      'else',
      ':',
      $.block,
    ),

    match_statement: $ => seq(
      'match',
      $.expression,
      ':',
      $._indent,
      repeat1($.case_clause),
      $._dedent,
    ),

    case_clause: $ => seq(
      'case',
      $.pattern,
      optional($.guard),
      ':',
      $.block,
    ),

    guard: $ => seq(
      'if',
      $.expression,
    ),

    for_statement: $ => seq(
      'for',
      $.pattern,
      'in',
      $.expression,
      ':',
      $.block,
    ),

    while_statement: $ => seq(
      'while',
      $.expression,
      ':',
      $.block,
    ),

    loop_statement: $ => seq(
      'loop',
      optional(seq(':', $.identifier)),
      ':',
      $.block,
    ),

    receive_block: $ => seq(
      'receive',
      ':',
      $._indent,
      repeat1($.case_clause),
      optional($.timeout_clause),
      $._dedent,
    ),

    timeout_clause: $ => seq(
      'after',
      $.expression,
      ':',
      $.block,
    ),

    context_block: $ => seq(
      'context',
      $.expression,
      ':',
      $.block,
    ),

    // if let pattern = expr: block
    if_let_statement: $ => seq(
      'if',
      'let',
      $.pattern,
      '=',
      $.expression,
      ':',
      $.block,
      optional($.else_clause),
    ),

    // while let pattern = expr: block
    while_let_statement: $ => seq(
      'while',
      'let',
      $.pattern,
      '=',
      $.expression,
      ':',
      $.block,
    ),

    // with expr as name: block
    with_statement: $ => seq(
      'with',
      commaSep1($.with_item),
      ':',
      $.block,
    ),

    with_item: $ => seq(
      $.expression,
      optional(seq('as', $.identifier)),
    ),

    //=========================================================================
    // PATTERNS
    //=========================================================================

    pattern: $ => choice(
      $.identifier_pattern,
      $.literal_pattern,
      $.wildcard_pattern,
      $.tuple_pattern,
      $.struct_pattern,
      $.enum_pattern,
      $.or_pattern,
      $.range_pattern,
      $.rest_pattern,
      $.typed_pattern,
    ),

    identifier_pattern: $ => $.identifier,

    literal_pattern: $ => choice(
      $.integer,
      $.float,
      $.string,
      $.boolean,
      $.nil,
      $.symbol,
    ),

    wildcard_pattern: $ => '_',

    tuple_pattern: $ => seq(
      '(',
      commaSep($.pattern),
      ')',
    ),

    struct_pattern: $ => seq(
      $.type_identifier,
      '(',
      commaSep($.field_pattern),
      ')',
    ),

    field_pattern: $ => seq(
      $.identifier,
      ':',
      $.pattern,
    ),

    enum_pattern: $ => seq(
      $.type_identifier,
      optional(seq('(', commaSep($.pattern), ')')),
    ),

    or_pattern: $ => prec.left(seq(
      $.pattern,
      '|',
      $.pattern,
    )),

    // Range patterns: 0..10, 'a'..'z'
    range_pattern: $ => seq(
      $.literal,
      '..',
      $.literal,
    ),

    // Rest pattern: *rest, used in tuple/array unpacking
    rest_pattern: $ => seq(
      '*',
      $.identifier,
    ),

    typed_pattern: $ => seq(
      $.identifier,
      ':',
      $.type,
    ),

    //=========================================================================
    // EXPRESSIONS
    //=========================================================================

    expression: $ => choice(
      $.primary_expression,
      $.unary_expression,
      $.binary_expression,
      $.comparison_expression,
      $.chained_comparison,
      $.logical_expression,
      $.functional_update_expression,
      $.try_expression,
      $.if_expression,
      $.match_expression,
      $.lambda_expression,
      $.move_lambda_expression,
      $.spawn_expression,
      $.new_expression,
      $.list_comprehension,
      $.dict_comprehension,
    ),

    primary_expression: $ => prec('primary', choice(
      $.identifier,
      $.literal,
      $.suffixed_literal,         // 100_km, 5_hr
      $.grouped_expression,
      $.tuple_expression,
      $.array_expression,
      $.dict_expression,
      $.struct_literal,
      $.call_expression,
      $.method_call_expression,
      $.field_access,
      $.index_expression,
      $.slice_expression,         // items[1:3], items[::2]
      $.do_block,                 // do: body (BDD DSL blocks)
      $.block_expression,         // Custom DSL blocks: m{...}, sh{...}, sql{...}
    )),

    identifier: $ => /[a-zA-Z_][a-zA-Z0-9_]*/,

    literal: $ => choice(
      $.type_suffixed_literal,  // 42i32, 3.14f64 (must be before integer/float)
      $.integer,
      $.float,
      $.string,
      $.char,
      $.boolean,
      $.nil,
      $.symbol,
    ),

    integer: $ => choice(
      $.decimal_integer,
      $.hex_integer,
      $.binary_integer,
      $.octal_integer,
    ),

    decimal_integer: $ => /[0-9][0-9_]*/,

    hex_integer: $ => /0[xX][0-9a-fA-F][0-9a-fA-F_]*/,

    binary_integer: $ => /0[bB][01][01_]*/,

    octal_integer: $ => /0[oO][0-7][0-7_]*/,

    float: $ => choice(
      /[0-9][0-9_]*\.[0-9][0-9_]*([eE][+-]?[0-9]+)?/,
      /0[xX][0-9a-fA-F][0-9a-fA-F_]*\.[0-9a-fA-F][0-9a-fA-F_]*[pP][+-]?[0-9]+/,  // hex float
    ),

    // Type suffix for explicit literal types: 42i32, 3.14f64
    type_suffixed_literal: $ => seq(
      choice($.integer, $.float),
      $.type_suffix,
    ),

    type_suffix: $ => choice(
      'i8', 'i16', 'i32', 'i64',
      'u8', 'u16', 'u32', 'u64',
      'f32', 'f64',
    ),

    string: $ => seq(
      $._string_start,
      repeat(choice(
        $._string_content,
        $.interpolation,
        $.escape_sequence,
      )),
      $._string_end,
    ),

    interpolation: $ => seq(
      '{',
      $.expression,
      '}',
    ),

    escape_sequence: $ => token.immediate(seq(
      '\\',
      choice(
        /[\\'"nrtbfv0]/,
        /x[0-9a-fA-F]{2}/,
        /u[0-9a-fA-F]{4}/,
        /U[0-9a-fA-F]{8}/,
      ),
    )),

    char: $ => seq(
      "'",
      choice(
        /[^'\\]/,
        $.escape_sequence,
      ),
      "'",
    ),

    boolean: $ => choice('true', 'false'),

    nil: $ => 'nil',

    symbol: $ => /:[a-zA-Z_][a-zA-Z0-9_]*/,

    grouped_expression: $ => seq('(', $.expression, ')'),

    tuple_expression: $ => seq(
      '(',
      $.expression,
      ',',
      commaSep($.expression),
      ')',
    ),

    array_expression: $ => seq(
      '[',
      commaSep($.expression),
      ']',
    ),

    dict_expression: $ => seq(
      '{',
      commaSep($.dict_entry),
      '}',
    ),

    dict_entry: $ => seq(
      $.expression,
      ':',
      $.expression,
    ),

    struct_literal: $ => seq(
      $.type_identifier,
      '(',
      commaSep($.field_argument),
      ')',
    ),

    // Both ':' and '=' are supported for argument assignment
    // with no preference (Pattern A - like 'pass' vs '()').
    // Examples: Point(x: 5) or Point(x = 5)
    field_argument: $ => seq(
      $.identifier,
      choice(':', '='),
      $.expression,
    ),

    call_expression: $ => prec('call', seq(
      $.primary_expression,
      '(',
      commaSep($.argument),
      ')',
    )),

    method_call_expression: $ => prec('call', seq(
      $.primary_expression,
      '.',
      $.identifier,
      optional(seq('(', commaSep($.argument), ')')),
      optional($.trailing_block),
    )),

    argument: $ => choice(
      $.expression,
      $.named_argument,
    ),

    // Both ':' and '=' are supported for argument assignment
    // with no preference (Pattern A - like 'pass' vs '()').
    // Examples: func(x: 42) or func(x = 42)
    named_argument: $ => seq(
      $.identifier,
      choice(':', '='),
      $.expression,
    ),

    trailing_block: $ => seq(
      $.lambda_params,
      ':',
      $.block,
    ),

    field_access: $ => prec('call', seq(
      $.primary_expression,
      '.',
      $.identifier,
    )),

    index_expression: $ => prec('call', seq(
      $.primary_expression,
      '[',
      $.expression,
      ']',
    )),

    // Slice expression: items[1:3], items[::2], items[::-1]
    slice_expression: $ => prec('call', seq(
      $.primary_expression,
      '[',
      optional($.expression),  // start
      ':',
      optional($.expression),  // end
      optional(seq(':', optional($.expression))),  // step
      ']',
    )),

    // Do block: sequence of statements evaluating to unit
    // Used for colon-block syntax in BDD DSL: describe "name": body
    do_block: $ => seq(
      'do',
      ':',
      $.block,
    ),

    // Custom block expression: m{...}, sh{...}, sql{...}, re{...}, etc.
    // DSL embedding with typed result based on block kind.
    // Supported kinds: m (math), sh (shell), sql, re (regex), md, html, graph, img
    block_expression: $ => seq(
      $.block_kind,
      '{',
      /[^}]*/,                    // Raw payload content
      '}',
    ),

    block_kind: $ => choice(
      'm',      // Math expressions
      'sh',     // Shell commands
      'sql',    // SQL queries
      're',     // Regular expressions
      'md',     // Markdown
      'html',   // HTML
      'graph',  // Graph/diagram
      'img',    // Image
    ),

    //=========================================================================
    // OPERATOR EXPRESSIONS
    //=========================================================================

    unary_expression: $ => prec('unary', choice(
      seq('-', $.expression),
      seq('not', $.expression),
      seq('!', $.expression),
      seq('~', $.expression),
      seq('&', $.expression),  // Reference
      seq('*', $.expression),  // Dereference
    )),

    binary_expression: $ => choice(
      prec.left('power', seq($.expression, '**', $.expression)),
      prec.left('multiplicative', seq($.expression, choice('*', '/', '%'), $.expression)),
      prec.left('additive', seq($.expression, choice('+', '-'), $.expression)),
      prec.left('shift', seq($.expression, choice('<<', '>>'), $.expression)),
      prec.left('bitwise_and', seq($.expression, '&', $.expression)),
      prec.left('bitwise_xor', seq($.expression, '^', $.expression)),
      prec.left('bitwise_or', seq($.expression, '|', $.expression)),
    ),

    comparison_expression: $ => prec.left('comparison', seq(
      $.expression,
      choice('==', '!=', '<', '>', '<=', '>=', 'is', 'in'),
      $.expression,
    )),

    // Chained comparisons: 0 < x < 10, a <= b < c
    chained_comparison: $ => prec.left('comparison', seq(
      $.expression,
      repeat1(seq(
        choice('<', '>', '<=', '>=', '==', '!='),
        $.expression,
      )),
    )),

    logical_expression: $ => choice(
      prec.left('logical_and', seq($.expression, choice('and', '&&'), $.expression)),
      prec.left('logical_or', seq($.expression, choice('or', '||'), $.expression)),
    ),

    // Functional update: obj->method()
    functional_update_expression: $ => prec.left('functional_update', seq(
      $.expression,
      '->',
      $.identifier,
      '(',
      commaSep($.argument),
      ')',
    )),

    //=========================================================================
    // SPECIAL EXPRESSIONS
    //=========================================================================

    // Try expression: expr? (error propagation)
    try_expression: $ => prec.left(seq(
      $.expression,
      '?',
    )),

    if_expression: $ => seq(
      'if',
      $.expression,
      ':',
      $.expression,
      'else',
      ':',
      $.expression,
    ),

    match_expression: $ => seq(
      'match',
      $.expression,
      ':',
      $._indent,
      repeat1($.case_arm),
      $._dedent,
    ),

    case_arm: $ => seq(
      'case',
      $.pattern,
      optional($.guard),
      ':',
      $.expression,
      $._newline,
    ),

    // Lambda: \x: body or \x, y: body
    lambda_expression: $ => prec('lambda', seq(
      $.lambda_params,
      ':',
      choice(
        $.expression,
        $.block,
      ),
    )),

    lambda_params: $ => seq(
      '\\',
      choice(
        // Simple params: \x or \x, y
        commaSep1($.lambda_param),
        // Typed params: \(x: Int, y: Int)
        seq('(', commaSep($.typed_lambda_param), ')'),
      ),
      optional(seq('->', $.type)),  // Return type
    ),

    lambda_param: $ => $.identifier,

    typed_lambda_param: $ => seq(
      $.identifier,
      ':',
      $.type,
    ),

    // Move closure: captures by value instead of reference
    move_lambda_expression: $ => prec('lambda', seq(
      'move',
      $.lambda_params,
      ':',
      choice(
        $.expression,
        $.block,
      ),
    )),

    //=========================================================================
    // COMPREHENSIONS
    //=========================================================================

    // List comprehension: [x * 2 for x in items if x > 0]
    list_comprehension: $ => seq(
      '[',
      $.expression,
      repeat1($.comprehension_clause),
      ']',
    ),

    // Dict comprehension: {k: v for k, v in pairs if k != ""}
    dict_comprehension: $ => seq(
      '{',
      $.expression,
      ':',
      $.expression,
      repeat1($.comprehension_clause),
      '}',
    ),

    comprehension_clause: $ => choice(
      $.for_clause,
      $.if_clause,
    ),

    for_clause: $ => seq(
      'for',
      $.pattern,
      'in',
      $.expression,
    ),

    if_clause: $ => seq(
      'if',
      $.expression,
    ),

    //=========================================================================
    // SPREAD EXPRESSIONS
    //=========================================================================

    // Spread in arrays: [*a, *b, 3]
    spread_element: $ => seq(
      '*',
      $.expression,
    ),

    // Spread in dicts: {**d1, **d2, "key": value}
    dict_spread: $ => seq(
      '**',
      $.expression,
    ),

    spawn_expression: $ => seq(
      'spawn',
      choice(
        $.call_expression,
        $.lambda_expression,
        $.type_identifier,  // Actor spawn
        seq($.type_identifier, '(', commaSep($.argument), ')'),
      ),
    ),

    // Memory allocation expressions
    new_expression: $ => choice(
      $.new_unique,
      $.new_shared,
      $.new_weak,
      $.new_handle,
    ),

    // new(&) T(...) -> &T
    new_unique: $ => seq(
      'new',
      '(',
      '&',
      ')',
      $.type_identifier,
      '(',
      commaSep($.argument),
      ')',
    ),

    // new* T(...) -> *T
    new_shared: $ => seq(
      'new',
      '*',
      $.type_identifier,
      '(',
      commaSep($.argument),
      ')',
    ),

    // new- T(...) -> -T
    new_weak: $ => seq(
      'new',
      '-',
      $.type_identifier,
      '(',
      commaSep($.argument),
      ')',
    ),

    // new+ T(...) -> +T
    new_handle: $ => seq(
      'new',
      '+',
      $.type_identifier,
      '(',
      commaSep($.argument),
      ')',
    ),

    //=========================================================================
    // COMMENTS
    //=========================================================================

    comment: $ => token(seq('#', /.*/)),
  },

  extras: $ => [
    $.comment,
    /[ \t]+/,
  ],
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

Back to: [Grammar Index](lexer_parser_grammar.md) | [Part 1: Definitions](lexer_parser_grammar_definitions.md)

Next: [External Scanner and Rust Bindings](lexer_parser_scanner.md)
