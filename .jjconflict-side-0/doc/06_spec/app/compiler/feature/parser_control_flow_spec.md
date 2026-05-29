# Parser Control Flow Specification

**Feature ID:** #PARSER-CF-001 to #PARSER-CF-020 | **Category:** Infrastructure | Parser | **Status:** Implemented

_Source: `test/feature/usage/parser_control_flow_spec.spl`_

---

## Syntax

```simple
if condition:
    body
elif condition:
    body
else:
    body

while condition:
    body

for item in collection:
    body

match value:
    case pattern:
        body

loop:
    body
    if done:
        break
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 33 |

## Test Structure

### If Statement Parsing

#### simple if

- ✅ parses if with single statement
- ✅ parses if with false condition
#### if-else

- ✅ parses if-else
#### if-elif-else

- ✅ parses multiple elif branches
#### nested if

- ✅ parses nested if statements
### While Loop Parsing

- ✅ parses while loop
- ✅ parses while with complex condition
- ✅ parses while false (no iterations)
### For Loop Parsing

- ✅ parses for-in with array
- ✅ parses for-in with range
- ✅ parses for-in with inclusive range
- ✅ parses for with tuple destructuring
### Match Statement Parsing

#### literal patterns

- ✅ parses match with integer patterns
#### guard clauses

- ✅ parses match with guards
#### enum patterns

- ✅ parses match with enum variants
#### tuple patterns

- ✅ parses match with tuple patterns
### Loop Statement Parsing

- ✅ parses loop with break
- ✅ parses loop with continue
### Suspension Control Flow Parsing

#### suspension if

- ✅ parses if~ statement
#### suspension while

- ✅ parses while~ statement
#### suspension for

- ✅ parses for~ statement
#### suspension assignment

- ✅ parses ~= assignment
### Return Statement Parsing

- ✅ parses return with value
- ✅ parses early return
- ✅ parses return without value
### If Val/Var and While Val Parsing

#### if val

- ✅ parses if val with Some
- ✅ parses if val with else
#### if var

- ✅ parses if var with Some
#### while val

- ✅ parses while val
#### while var

- ✅ parses while var
### Complex Control Flow Parsing

- ✅ parses nested loops
- ✅ parses mixed control flow
- ✅ parses deeply nested conditions

