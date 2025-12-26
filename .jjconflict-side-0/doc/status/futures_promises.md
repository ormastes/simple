# Feature #48: Futures and Promises

**Status**: Partial
**Difficulty**: 3 (was 4)
**Importance**: 4

## Summary

Async/await syntax for asynchronous programming with futures.

## Current Implementation

- [x] `async` keyword (lexer/parser)
- [x] `await` expression (lexer/parser)
- [x] AST: `Expr::Spawn`, `Expr::Await`
- [x] Effect annotation on functions

## Parsed Syntax

```simple
async fn fetch_data() -> str:
    let response = await http_get("https://example.com")
    return response.body

# Currently parsed but not fully executed
let future = fetch_data()
let result = await future
```

## Remaining Work

- [ ] Future type in type system
- [ ] Async runtime/executor
- [ ] Proper await semantics (suspend/resume)
- [ ] Future combinators (map, then, all, race)

## Why Difficulty Reduced (4→3)

- async/await keywords already parsed
- Spawn/Await expressions in AST
- Effect system has async variant
- Can build on existing spawn infrastructure
- Executor is well-understood pattern (can use tokio or simple poll loop)

## Tests

- Basic spawn expression works
- Full async/await needs runtime

## Dependencies

- #31 Concurrency Primitives (fixing channels helps here too)
- Async runtime implementation

## Files

- `src/parser/src/lexer.rs` - async/await keywords
- `src/parser/src/parser.rs` - async fn, await expr
- `src/parser/src/ast.rs` - Effect::Async, Expr::Await

## Related

- #30 Actors
- #31 Concurrency
- #33 Stackless Coroutines
