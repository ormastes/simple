# Loop Constructs Specification

The Simple language provides several loop constructs for iterating over collections and

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1100 |
| Category | Syntax |
| Status | Implemented |
| Source | `test/feature/usage/loops_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

The Simple language provides several loop constructs for iterating over collections and
executing code repeatedly. Loop types include while loops for condition-based iteration,
for loops for collection iteration, and comprehensions for creating collections from
iterative expressions. All loops support break and continue flow control.

## Syntax

```simple
var i = 0
while i < 10:
print i
i = i + 1

for item in items:
print item

for i in 0..10:
print i

[for x in items if x > 5: x * 2]

{for x in items: (x, x * 2)}
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| While Loop | Condition-based repetition until condition becomes false |
| For Loop | Iteration over collection elements with implicit binding |
| Range | Sequence of values from start to end (inclusive or exclusive) |
| Comprehension | Concise syntax for building collections from iterations |
| Break Statement | Exit loop immediately |
| Continue Statement | Skip to next loop iteration |

## Behavior

Loop constructs:
- Execute code zero or more times based on conditions or collection size
- Support break and continue for flow control
- Provide implicit iteration variables in for loops
- Enable collection creation through comprehensions
- Work with ranges and user-defined iterables
- Support nested loops and complex conditions

## Related Specifications

- Range Expressions (start..end syntax)
- Collection Types (List, Dict, Set iteration)
- Pattern Matching (destructuring in for loops)
- Lambda Expressions (used in functional iteration)

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/loops/result.json` |

## Scenarios

- executes while loop with condition
- exits while loop when condition becomes false
- handles while loop with break
- handles while loop with continue
- iterates over exclusive range
- iterates over inclusive range
- handles negative ranges
- iterates over list
- iterates with break
- iterates with continue
- executes nested loops
- breaks outer loop from nested loop
- creates list from range
- filters with comprehension
- transforms and filters
- comprehension over existing collection
- iterates with positive step
- iterates with negative step
- creates dict from range
- nested comprehension
- conditional nesting in comprehension
