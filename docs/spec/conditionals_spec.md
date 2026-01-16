# Conditionals (If/Elif/Else)

*Source: `simple/std_lib/test/features/control_flow/conditionals_spec.spl`*

---

# Conditionals (If/Elif/Else)

**Feature ID:** #91
**Category:** Control Flow
**Difficulty:** 2/5 (Beginner-Intermediate)
**Status:** Complete

## Overview

Conditional statements in Simple provide branching control flow based on boolean expressions.
Following Python's syntax, Simple uses `if`, `elif` (else-if), and `else` keywords with
indentation-based blocks for readable, structured decision making.

**Key Features:**
- **If statements:** Execute block when condition is true
- **Elif chains:** Test multiple conditions in sequence
- **Else clause:** Execute when all previous conditions are false
- **Boolean expressions:** Support for `and`, `or`, `not` logical operators
- **Comparison operators:** `==`, `!=`, `<`, `>`, `<=`, `>=`
- **Truthy values:** All values have truthiness (non-zero, non-empty, non-None)

## Syntax

### If Statement

```simple
if condition:
    # Execute when condition is true
    statement1
    statement2
```

**Grammar:**
```
if_stmt = 'if' expression ':' NEWLINE INDENT statement+ DEDENT
```

### If-Else Statement

```simple
if condition:
    # Execute when true
    result = "yes"
else:
    # Execute when false
    result = "no"
```

**Grammar:**
```
if_else = 'if' expression ':' block 'else' ':' block
```

### If-Elif-Else Chain

```simple
if score >= 90:
    grade = "A"
elif score >= 80:
    grade = "B"
elif score >= 70:
    grade = "C"
else:
    grade = "F"
```

**Grammar:**
```
if_elif_else = 'if' expression ':' block ('elif' expression ':' block)* ('else' ':' block)?
```

### Boolean Operators

```simple
# Logical AND
if age >= 18 and has_license:
    can_drive = true

# Logical OR
if is_weekend or is_holiday:
    is_off_day = true

# Logical NOT
if not is_raining:
    go_outside = true

# Complex expressions
if (a > 0 and b > 0) or c == 0:
    proceed = true
```

## Runtime Representation

**Condition Evaluation:**
Conditions are evaluated to boolean values:
    ```rust
pub fn eval_condition(&mut self, expr: &Expression) -> Result<bool, Error> {
    let value = self.eval_expression(expr)?;
    Ok(value.is_truthy())  // Convert to boolean
}
```

**Truthiness Rules:**
```rust
impl RuntimeValue {
    pub fn is_truthy(&self) -> bool {
        match self {
            RuntimeValue::Bool(b) => *b,
            RuntimeValue::Int(n) => *n != 0,
            RuntimeValue::Float(f) => *f != 0.0,
            RuntimeValue::Text(s) => !s.is_empty(),
            RuntimeValue::None => false,
            RuntimeValue::List(l) => !l.is_empty(),
            _ => true,  // Objects, functions are truthy
        }
    }
}
```

**Execution Flow:**
1. Evaluate `if` condition
2. If true → execute if block, skip rest
3. If false → try next `elif` (if exists)
4. Repeat until a condition is true
5. If all false → execute `else` block (if exists)
6. If no `else` and all false → skip entire statement

## Comparison with Other Languages

| Feature | Simple | Python | JavaScript | Rust | Scala |
|---------|--------|--------|------------|------|-------|
| If syntax | `if cond:` | `if cond:` | `if (cond) {}` | `if cond {}` | `if (cond) {}` |
| Elif | `elif` | `elif` | `else if` | `else if` | `else if` |
| Else | `else:` | `else:` | `else {}` | `else {}` | `else {}` |
| Boolean operators | `and`, `or`, `not` | `and`, `or`, `not` | `&&`, `||`, `!` | `&&`, `||`, `!` | `&&`, `||`, `!` |
| Truthiness | Implicit | Implicit | Implicit | ❌ Explicit only | Explicit |
| If as expression | ❌ Statement | ❌ Statement | ✅ Ternary | ✅ Yes | ✅ Yes |

**Key Similarities:**
- Python-like syntax with colons and indentation
- Same truthiness semantics as Python
- Natural language operators (`and`/`or`/`not`)

**Key Differences:**
- Simple: If is statement (not expression yet)
- Rust: No implicit truthiness, must be explicit bool
- JavaScript: Uses C-style symbols (`&&`, `||`)

## Common Patterns

### Guard Clauses
```simple
fn process_user(user):
    if user == nil:
        return "error: no user"

    if not user.is_active:
        return "error: inactive user"

    # Main logic here
    return "success"
```

### Validation Chains
```simple
if name == "":
    error = "Name required"
elif age < 0:
    error = "Invalid age"
elif email == "":
    error = "Email required"
else:
    error = nil  # Valid
```

### Range Checking
```simple
if score < 0 or score > 100:
    print("Invalid score")
elif score >= 90:
    grade = "A"
elif score >= 80:
    grade = "B"
else:
    grade = "F"
```

### Complex Boolean Logic
```simple
if (is_admin or is_owner) and not is_suspended:
    access_granted = true
else:
    access_granted = false
```

## Implementation Files

**Parser:** `src/parser/src/statements/mod.rs` - If/elif/else parsing
**Interpreter:** `src/compiler/src/interpreter_control.rs` - Condition evaluation, branch execution
**Runtime:** `src/runtime/src/value/core.rs` - Truthiness implementation
**Tests:** `src/driver/tests/interpreter_control.rs` - Control flow tests

## Related Features

- **Boolean Operators (#TBD):** `and`, `or`, `not` logical operations
- **Comparison Operators (#TBD):** `==`, `!=`, `<`, `>`, `<=`, `>=`
- **Match Expressions (#90):** Pattern matching (more powerful than if/elif)
- **Loops (#13):** While loops use conditional expressions
- **Ternary Operator (#planned):** If-as-expression for simple cases

## Performance Characteristics

| Operation | Time | Notes |
|-----------|------|-------|
| Condition evaluation | O(1) | Simple boolean or comparison |
| Complex boolean expr | O(n) | n = number of operators |
| Branch execution | O(m) | m = statements in executed branch |
| Elif chain | O(k) | k = number of conditions checked |

**Optimization:** Short-circuit evaluation for `and`/`or`:
    - `a and b` → if `a` is false, don't evaluate `b`
- `a or b` → if `a` is true, don't evaluate `b`

## Limitations and Future Work

**Current Limitations:**
- If is a statement, not an expression (can't assign `val x = if ... else ...`)
- No ternary operator (`cond ? a : b`)
- No switch/case (use match instead)
- No pattern matching in if conditions

**Planned Features:**
- If-expressions: `val result = if cond: a else: b`
- Ternary operator: `val x = cond ? a : b`
- Pattern guards: `if let Some(x) = option:`
- Unless statement: `unless cond: ...` (syntactic sugar for `if not`)

## If Statements - Basic Conditional Execution

    If statements execute a block of code when a boolean condition evaluates to true.
    If the condition is false, the block is skipped entirely.

    **Syntax:** `if condition: block`

    **Truthiness:**
    - `true` → truthy
    - `false`, `0`, `""`, `nil`, `[]` → falsy
    - All other values → truthy

    **Implementation:** `src/compiler/src/interpreter_control.rs:interpret_if()`

**Given** an if statement with a true condition
        **When** the if statement is executed
        **Then** the if block executes and the variable is set

        **Example:**
        ```simple
        var result = 0
        if true:
            result = 1
        assert result == 1
        ```

        **Runtime:** Condition evaluates to `true`, block executes

**Given** an if statement with a false condition
            **When** the if statement is executed
            **Then** the if block is skipped and the variable remains unchanged

            **Example:**
            ```simple
            var value = 0
            if false:
                value = 1
            assert value == 0  # Unchanged
            ```

            **Runtime:** Condition evaluates to `false`, block skipped

**Given** an if statement with a comparison expression
            **When** the expression evaluates to true
            **Then** the if block executes

            **Example:**
            ```simple
            var check = 0
            if 5 > 3:
                check = 1
            assert check == 1
            ```

            **Common Comparisons:**
            - `a == b` - equality
            - `a != b` - inequality
            - `a < b`, `a > b` - less/greater than
            - `a <= b`, `a >= b` - less/greater or equal

## Else Clauses - Fallback Execution

    Else clauses provide a fallback block that executes when the if condition is false.
    The else block is mutually exclusive with the if block - exactly one executes.

    **Syntax:**
    ```simple
    if condition:
        # Execute if true
    else:
        # Execute if false
    ```

    **Property:** One and only one block executes (if OR else, never both, never neither)

**Given** an if-else statement where the if condition is false
        **When** the statement is executed
        **Then** the else block executes

        **Example:**
        ```simple
        var result = 0
        if false:
            result = 1
        else:
            result = 2
        assert result == 2  # Else executed
        ```

        **Pattern:** Binary choice - one of two paths

**Given** an if-else statement where the if condition is true
            **When** the statement is executed
            **Then** the if block executes and else is skipped

            **Example:**
            ```simple
            var value = 0
            if true:
                value = 1
            else:
                value = 2
            assert value == 1  # If executed, else skipped
            ```

            **Mutual Exclusivity:** Never execute both blocks

## Elif Chains - Multiple Conditions

    Elif (else-if) allows testing multiple conditions in sequence. The first condition
    that evaluates to true has its block executed, and the rest are skipped.

    **Syntax:**
    ```simple
    if condition1:
        # Block 1
    elif condition2:
        # Block 2
    elif condition3:
        # Block 3
    else:
        # Fallback
    ```

    **Execution:** First-match wins - test in order, execute first true, skip rest
    **Use Case:** Multi-way branching (grade assignment, categorization, routing)

**Given** an if-elif-else chain
        **When** the second condition is true
        **Then** the elif block executes and remaining conditions are skipped

        **Example:**
        ```simple
        var grade = ""
        var score = 85
        if score >= 90:
            grade = "A"
        elif score >= 80:
            grade = "B"  # This executes
        elif score >= 70:
            grade = "C"
        else:
            grade = "F"
        assert grade == "B"
        ```

        **Short-circuit:** Once a condition matches, remaining elif/else are skipped

**Given** an if-elif-else chain where all conditions are false
            **When** the statement is executed
            **Then** the else block executes

            **Example:**
            ```simple
            var result = ""
            if 1 > 2:
                result = "A"
            elif 2 > 3:
                result = "B"
            else:
                result = "C"  # All conditions false, else executes
            assert result == "C"
            ```

            **Pattern:** Exhaustive branching - else catches all unmatched cases

## Boolean Operators - Logical Combinations

    Boolean operators combine multiple conditions into complex expressions.
    Simple uses natural language operators (`and`, `or`, `not`) like Python.

    **Operators:**
    - `and` - both conditions must be true
    - `or` - at least one condition must be true
    - `not` - negates the condition

    **Short-circuit Evaluation:**
    - `a and b` - if `a` is false, don't evaluate `b`
    - `a or b` - if `a` is true, don't evaluate `b`

    **Precedence:** `not` > `and` > `or`

**Given** an if statement with an `and` expression
        **When** both conditions are true
        **Then** the block executes

        **Truth Table:**
        ```
        true  and true  → true
        true  and false → false
        false and true  → false
        false and false → false
        ```

        **Use Case:** Multiple requirements must all be satisfied

**Given** an if statement with an `or` expression
            **When** at least one condition is true
            **Then** the block executes

            **Truth Table:**
            ```
            true  or true  → true
            true  or false → true
            false or true  → true
            false or false → false
            ```

            **Use Case:** Any of several conditions can trigger action

**Given** an if statement with a `not` expression
            **When** the condition is false (negated to true)
            **Then** the block executes

            **Negation:**
            - `not true` → false
            - `not false` → true

            **Use Case:** Execute when condition is NOT met
