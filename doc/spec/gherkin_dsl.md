```simple
# file: calculator_system_test.simple

"""
# Calculator System Test

Comprehensive BDD test suite for Calculator operations.

## Overview

This specification validates arithmetic operations, state management,
and edge case handling for the Calculator class.

## Test Data

### Addition Examples
${examples addition}

### Operation Examples
${examples operation}

### Identity Examples
${examples identity}

## Features
"""


"""
## Examples

Reusable test data tables for parameterized scenarios.
"""

examples addition:
    """
    Test data for basic addition operations.
    Covers positive, negative, and zero cases.
    """
    a    b    result
    1    2    3
    10   20   30
    -5   10   5
    0    0    0

examples operation:
    """
    Mixed operations with various starting values.
    Tests add, multiply, subtract, divide.
    """
    start  operation       result
    10     add 5           15
    10     multiply by 2   20
    100    subtract 30     70
    50     divide by 5     10

examples identity:
    """
    Mathematical identity properties.
    Adding 0 or multiplying by 1 preserves value.
    """
    n   operation
    42  add 0
    42  multiply by 1
    99  add 0
    7   multiply by 1

examples division:
    """
    Valid division cases.
    All results are integers (no remainder).
    """
    dividend  divisor  result
    10        2        5
    100       4        25
    9         3        3


"""
## Context Definitions

Reusable step definitions for Given/When/Then.
"""

context fresh calculator:
    """A new calculator instance with value 0"""
    calc = Calculator.new()

context calculator at <n>:
    """Calculator initialized with value <n>"""
    calc = Calculator.new().set(n)

context add <n>:
    """Add <n> to current value"""
    calc = calc.add(n)

context subtract <n>:
    """Subtract <n> from current value"""
    calc = calc.subtract(n)

context multiply by <n>:
    """Multiply current value by <n>"""
    calc = calc.multiply(n)

context divide by <n>:
    """Divide current value by <n>"""
    calc = calc.divide(n)

context value is <n>:
    """Assert current value equals <n>"""
    calc.value == n

context history is empty:
    """Assert no operations recorded"""
    calc.history.empty?

context history has <n> entries:
    """Assert history contains <n> operations"""
    calc.history.size == n


"""
## Features
"""

feature Basic Calculator Operations:
    """
    Core operations on a fresh calculator.
    Validates initial state and single operations.
    """
    
    scenario New calculator starts at zero:
        """Verify default initialization"""
        given fresh calculator:
        then value is 0:
        and_then history is empty:
    
    scenario Adding a number:
        """Single addition from zero"""
        given fresh calculator:
        when add 5:
        then value is 5:
        and_then history has 1 entries:
    
    scenario Subtracting from zero:
        """Subtraction resulting in negative"""
        given fresh calculator:
        when subtract 3:
        then value is -3:


feature Parameterized Addition:
    """
    Addition with multiple inputs.
    Uses table-driven test data.
    """
    
    scenario outline Adding two numbers:
        """Add <a> then <b>, expect <result>"""
        given fresh calculator:
        when add <a>:
        when add <b>:
        then value is <result>:
        
        examples addition:


feature Parameterized Operations:
    """
    Various operations with different starting values.
    """
    
    scenario outline Operations with initial value:
        """Start at <start>, apply <operation>, expect <result>"""
        given calculator at <start>:
        when <operation>:
        then value is <result>:
        
        examples operation:


feature Arithmetic Properties:
    """
    Mathematical identity properties.
    x + 0 = x, x * 1 = x
    """
    
    scenario outline Identity operations:
        """Value <n> unchanged after <operation>"""
        given calculator at <n>:
        when <operation>:
        then value is <n>:
        
        examples identity:


feature Division:
    """
    Division behavior including error cases.
    """
    
    scenario outline Valid division:
        """Divide <dividend> by <divisor>"""
        given calculator at <dividend>:
        when divide by <divisor>:
        then value is <result>:
        
        examples division:
    
    scenario Division by zero:
        """Error when dividing by zero"""
        given calculator at 10:
        then raises DivisionByZeroError:
            calc.divide(0)


feature Chained Operations:
    """
    Multiple operations in sequence.
    """
    
    scenario Add then multiply:
        """Chain: 0 + 5 * 2 = 10"""
        given fresh calculator:
        when add 5:
        when multiply by 2:
        then value is 10:
        and_then history has 2 entries:
    
    scenario Complex chain:
        """Chain: 100 - 20 / 4 = 20"""
        given calculator at 100:
        when subtract 20:
        when divide by 4:
        then value is 20:


feature Inline Examples:
    """
    Demonstrating inline table definition.
    """
    
    scenario outline Custom addition:
        """Inline examples within scenario"""
        given fresh calculator:
        when add <x>:
        when add <y>:
        then value is <sum>:
        
        examples:
            x    y    sum
            100  200  300
            -10  10   0
    
    scenario outline Named inline:
        """Named inline for reuse clarity"""
        given calculator at <start>:
        when multiply by <factor>:
        then value is <product>:
        
        examples multiplication:
            start  factor  product
            5      4       20
            7      3       21
            0      100     0
```

---

## Syntax Reference

### Keywords

| Form | Meaning |
|------|---------|
| `examples name:` | Named examples table (two-space delimiter) |
| `context pattern:` | Step definition with `<placeholder>` support |
| `feature name:` | Feature grouping |
| `scenario name:` | Single test case |
| `scenario outline name:` | Parameterized test with examples |
| `given/when/then/and_then pattern:` | Step references |
| `"""..."""` | Doc comment (any level) |
| `${examples name}` | Embed table in documentation |

### Table Kind Types (SDN Integration)

| Kind | Syntax | Colon | Delimiter | Use Case |
|------|--------|-------|-----------|----------|
| **Typed table** | `name: table{i32, i32}` | ✅ | Comma | Strongly-typed data |
| **Named table** | `name \|f1, f2\|` | ❌ | Comma | SDN configuration |
| **Examples table** | `examples name:` | ✅ | Two-space | BDD test data |

### Two-Space Delimiter

Examples tables use **two or more spaces** as column delimiter:

```
start  operation       result    # header row
10     add 5           15        # "add 5" is single value (one space)
10     multiply by 2   20        # "multiply by 2" is single value
```

- Single space → part of value
- Two+ spaces → column boundary

---

## Grammar (EBNF)

### One-Pass LL(2) Parser

All constructs can be parsed with maximum 2-token lookahead.

```ebnf
(* === TOP LEVEL === *)
document      = statement* ;

statement     = examples_stmt
              | context_stmt
              | feature_stmt
              | named_table       (* SDN: name |fields| *)
              | typed_table       (* SDN: name: table{...} *)
              | value_stmt        (* SDN: name: value *)
              ;

(* === BDD CONSTRUCTS === *)

examples_stmt = 'examples' IDENT ':' NEWLINE INDENT
                doc_comment?
                header_row
                data_row+
                DEDENT ;

context_stmt  = 'context' step_pattern ':' NEWLINE INDENT
                doc_comment?
                (statement | expr)+
                DEDENT ;

feature_stmt  = 'feature' description ':' NEWLINE INDENT
                doc_comment?
                scenario_stmt+
                DEDENT ;

scenario_stmt = 'scenario' 'outline'? description ':' NEWLINE INDENT
                doc_comment?
                step_ref+
                examples_ref?
                DEDENT ;

step_ref      = ('given' | 'when' | 'then' | 'and_then') step_pattern ':'
                (NEWLINE | INDENT block DEDENT) ;

examples_ref  = 'examples' IDENT? ':'
                (NEWLINE | INDENT inline_examples DEDENT) ;

inline_examples = header_row data_row+ ;

(* === STEP PATTERNS === *)

step_pattern  = pattern_part+ ;
pattern_part  = IDENT | NUMBER | '<' IDENT '>' ;   (* <n> = placeholder *)

description   = (IDENT | NUMBER | SYMBOL)+ ;

(* === TWO-SPACE DELIMITED ROWS === *)

header_row    = value (TWO_SPACES value)* NEWLINE ;
data_row      = value (TWO_SPACES value)* NEWLINE ;

TWO_SPACES    = '  ' ' '* ;   (* 2+ consecutive spaces *)

(* === SDN TABLES (unchanged) === *)

named_table   = IDENT '|' field_list '|'
                (row | NEWLINE INDENT rows DEDENT) ;

typed_table   = IDENT ':' 'table' '{' type_list '}'
                ('=' '[' tuple_list ']' | NEWLINE INDENT rows DEDENT) ;

field_list    = IDENT (',' IDENT)* ;
type_list     = IDENT (',' IDENT)* ;
rows          = row+ ;
row           = value (',' value)* NEWLINE ;

(* === DOC COMMENTS === *)

doc_comment   = '"""' doc_content '"""' NEWLINE ;
doc_content   = (CHAR | interpolation)* ;
interpolation = '${' 'examples' IDENT '}' ;

(* === TOKENS === *)

IDENT         = [A-Za-z_][A-Za-z0-9_]* ;
NUMBER        = '-'? [0-9]+ ('.' [0-9]+)? ;
NEWLINE       = '\n' | '\r\n' ;
INDENT        = <increase in indentation> ;
DEDENT        = <decrease in indentation> ;
```

### Parse Decision Tree (LL(2))

```
parse_statement():
    tok = peek()
    next = peek(2)

    switch tok:
        case 'examples':       → parse_examples_stmt()
        case 'context':        → parse_context_stmt()
        case 'feature':        → parse_feature_stmt()
        case 'scenario':       → parse_scenario_stmt()
        case 'given'|'when'|'then'|'and_then':
                               → parse_step_ref()
        case IDENT:
            switch next:
                case '|':      → parse_named_table()   # no colon!
                case ':':
                    if peek(3) == 'table':
                               → parse_typed_table()
                    else:      → parse_value_stmt()
```

### Lookahead Requirements

| Context | Lookahead | Decision |
|---------|-----------|----------|
| `examples` | 1 | Examples statement |
| `context` | 1 | Context definition |
| `feature` | 1 | Feature block |
| `scenario` | 1-2 | Scenario or scenario outline |
| `IDENT \|` | 2 | Named table (no colon) |
| `IDENT : table` | 3 | Typed table |
| `IDENT :` | 2 | Value or block |

---

## Relationship to Other Specs

| Spec | Purpose | Integration |
|------|---------|-------------|
| [SDN](spec/sdn.md) | Data notation | Table syntax (`\|fields\|`, `table{types}`) |
| [BDD Spec](spec/bdd_spec.md) | Test framework | `describe`, `context`, `it`, matchers |
| [Test Policy](guides/test.md) | Coverage & mocks | Test levels, coverage metrics |
| This doc | System test DSL | Gherkin-style `feature`/`scenario`/`examples` |

---

## Implementation Status

| Component | Status | Notes |
|-----------|--------|-------|
| Grammar spec | ✅ | This document |
| Parser keywords | 📋 | `examples`, `feature`, `scenario`, `given`, `when`, `then` |
| Two-space lexer mode | 📋 | Context-aware delimiter detection |
| Step pattern matching | 📋 | `<placeholder>` extraction |
| Examples interpolation | 📋 | `${examples name}` in doc comments |
| Living doc generation | ✅ | HTML/Markdown from BDD specs |
