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

**Syntax:**

| Form | Meaning |
|------|---------|
| `examples name:` + block | Named examples with data |
| `context name:` + block | Named context definition |
| `feature name:` + block | Feature grouping |
| `scenario name:` + block | Single test case |
| `scenario outline name:` + block | Parameterized test |
| `"""..."""` | Doc comment (any level) |
| `${examples name}` | Embed table in doc |
