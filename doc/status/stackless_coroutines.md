# Feature #33: Stackless Coroutine Actors

**Status**: Implemented
**Difficulty**: 4 (was 5)
**Importance**: 3

## Summary

Stackless coroutines enable lightweight, suspendable generators without dedicated stacks.

## Implemented Syntax

```simple
# Create a generator using a lambda with yield expressions
let gen = generator(\: [yield 1, yield 2, yield 3])

# Get values one at a time
let first = next(gen)   # 1
let second = next(gen)  # 2
let third = next(gen)   # 3
let fourth = next(gen)  # nil (exhausted)

# Collect all remaining values into an array
let gen2 = generator(\: [yield 10, yield 20])
let arr = collect(gen2)  # [10, 20]
```

## Features Implemented

- [x] `yield` keyword for suspension/value production
- [x] `generator()` built-in function to create generators from lambdas
- [x] `next()` built-in function to get the next value
- [x] `collect()` built-in function to gather all values into an array
- [x] Generator state tracking (Created, Suspended, Completed)
- [x] Shared generator state across clones (iteration continues)
- [x] Nil return when generator is exhausted

## Implementation Details

### Parser Changes
- Added `TokenKind::Yield` keyword to lexer
- Added `Expr::Yield(Option<Box<Expr>>)` to AST
- Yield parsing in `parse_unary()` - can be bare `yield` or `yield expr`

### Runtime Implementation
- `GeneratorValue` struct with:
  - `values: Arc<Mutex<Vec<Value>>>` - pre-computed yielded values
  - `index: Arc<Mutex<usize>>` - current position
  - `state: Arc<Mutex<GeneratorState>>` - tracks Created/Suspended/Completed
- Uses simple accumulation model where all yields are collected upfront
- Generator clones share state (Arc) so iteration is shared
- Thread-local `GENERATOR_YIELDS` for collecting yields during lambda execution

### Built-in Functions
- `generator(lambda)` - Creates generator by executing lambda, collecting yields
- `next(gen)` - Returns next value or nil if exhausted
- `collect(gen)` - Returns array of all remaining values

### How It Works
1. `generator(\: ...)` creates a lambda
2. Lambda body is executed with `GENERATOR_YIELDS` set up
3. Each `yield expr` adds `expr` result to yields list
4. After execution, yields are wrapped in `GeneratorValue`
5. `next()` returns values from the accumulated list
6. When list is exhausted, returns nil

## Tests

- `interpreter_generator_basic` - Multiple yields in array expression
- `interpreter_generator_single` - Single yield generator
- `interpreter_generator_collect` - Collect all values into array
- `interpreter_generator_exhausted` - Returns nil when done

## Limitations

This is a simplified "eager" generator implementation that:
- Evaluates all yields upfront (not lazy)
- Doesn't support true suspension/resumption
- Cannot handle infinite generators
- Does not transform to state machine (future enhancement)

## Related

- #30 Actors (Implemented)
- #31 Concurrency Primitives (Implemented)
- #32 Async Effects (Implemented)
- #48 Futures and Promises (Implemented)
