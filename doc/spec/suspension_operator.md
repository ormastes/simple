# Suspension Operator (`~`) Specification

**Status:** Draft
**Feature IDs:** #270-275
**Last Updated:** 2026-01-05
**Keywords:** async, suspension, await, effects, concurrency
**Topics:** concurrency, syntax, effects

This document specifies the `~` suspension operator for explicit suspension points in Simple's async execution model.

## Related Specifications

- [Async Default](async_default.md) - Async-by-default function model
- [Concurrency](concurrency.md) - Async/await, futures, actors
- [Syntax](syntax.md) - Core language syntax
- [Functions](functions.md) - Function definitions and effects

---

## Motivation

Simple uses async-by-default functions where suspension can occur implicitly. However, implicit suspension in control flow guards creates reasoning challenges:

```simple
# Problem: Is this condition suspending? Hard to tell at a glance.
if fetch_status() == Ready:
    proceed()

while not server.is_up():   # Does this suspend each iteration?
    retry()
```

The `~` operator makes suspension **explicit at the syntax level**, improving:

1. **Readability** - Suspension points visible without checking function signatures
2. **Reasoning** - Control flow behavior is immediately apparent
3. **Safety** - Compiler enforces suspension rules per context

---

## Overview

The `~` operator marks expressions that may suspend (perform async operations). It appears in three contexts:

| Context | Syntax | Meaning |
|---------|--------|---------|
| Assignment | `x ~= expr` | Evaluate `expr` (may suspend), assign result to `x` |
| If guard | `if~ cond:` | Evaluate `cond` (may suspend), branch on result |
| While guard | `while~ cond:` | Evaluate `cond` each iteration (may suspend) |

---

## Syntax

### Suspending Assignment (`~=`)

```simple
# Basic suspending assignment
let user: User ~= fetch_user(id)

# Type inference works
let data ~= load_data()

# Mutable variable
let mut counter ~= get_initial_count()
counter ~= refresh_count()

# Discard result (await and ignore)
_ ~= timer.sleep(100_ms)
```

**Semantics:**
- Right-hand side is evaluated; if it returns a `Future[T]`, it is awaited
- Result is assigned to the left-hand side
- Equivalent to: `let user = await fetch_user(id)`

### Suspending If Guard (`if~`)

```simple
# Suspending condition
if~ is_server_ready():
    start_processing()
elif~ fallback_available():
    use_fallback()
else:
    fail()

# Multiple conditions (all may suspend)
if~ check_auth() and~ has_permission():
    allow()
```

**Semantics:**
- Guard expression may perform async operations
- Each `elif~` may also suspend independently
- Plain `elif` after `if~` must be non-suspending

### Suspending While Guard (`while~`)

```simple
# Poll until ready
while~ not is_ready():
    _ ~= timer.sleep(100_ms)
    log("Waiting...")

# Process stream
while~ let Some(item) = stream.next():
    process(item)
```

**Semantics:**
- Condition is re-evaluated (and may suspend) on each iteration
- Loop body executes only when condition is true
- Supports pattern matching with `let`

### Suspending For Loop

```simple
# Async iterator
for~ item in async_stream():
    process(item)

# Equivalent to:
while~ let Some(item) = async_stream.next():
    process(item)
```

---

## Grammar (LL(1) Compatible)

The `~` token is recognized by the lexer as a distinct operator. Grammar extensions:

```ebnf
# Statements
IfStmt      -> "if" SuspendMark Expr ":" Block ElifClauses ElseClause?
ElifClauses -> { "elif" SuspendMark Expr ":" Block }
ElseClause  -> "else" ":" Block

WhileStmt   -> "while" SuspendMark Expr ":" Block

ForStmt     -> "for" SuspendMark Pattern "in" Expr ":" Block

SuspendMark -> "~" | ε

# Assignment
LetStmt     -> "let" ["mut"] Pattern [":" Type] AssignOp Expr
AssignStmt  -> LValue AssignOp Expr

AssignOp    -> "=" | "~=" | "+=" | "-=" | "*=" | "/=" | "%="
            | "~+=" | "~-=" | "~*=" | "~/=" | "~%="

# Expression-level (for chained conditions)
AndExpr     -> CompareExpr { ("and" | "and~") CompareExpr }
OrExpr      -> AndExpr { ("or" | "or~") AndExpr }
```

### Lexer Tokens

```
TILDE       = '~'
TILDE_EQ    = '~='
TILDE_PLUS_EQ  = '~+='
TILDE_MINUS_EQ = '~-='
# ... other compound assignments

# Keywords with tilde suffix (contextual)
IF_SUSPEND    = 'if' followed by '~' (no space required)
WHILE_SUSPEND = 'while' followed by '~'
FOR_SUSPEND   = 'for' followed by '~'
AND_SUSPEND   = 'and~'
OR_SUSPEND    = 'or~'
```

**Disambiguation:**
- `if~` vs `if ~expr`: Lexer treats `if~` as a unit when `~` immediately follows `if`
- `~=` is always the suspending assignment operator
- `~ =` (with space) is a unary `~` followed by `=` (parse error in assignment context)

---

## Effect System Integration

### Effect Annotations

Simple tracks suspension as an effect:

```simple
# Non-suspending (sync) function
sync fn compute(x: i64) -> i64:
    return x * 2

# May-suspend function (default for fn)
fn fetch_data() -> Data:
    let response ~= http.get(url)
    return parse(response)

# Explicitly async
async fn process() -> Result:
    ...
```

### Effect Rules

| Context | `=`, `if`, `while` | `~=`, `if~`, `while~` |
|---------|--------------------|-----------------------|
| `sync fn` | ✅ Allowed | ❌ Compile error |
| `fn` (default) | Non-suspending only | Suspending allowed |
| `async fn` | Non-suspending only | Suspending allowed |
| Actor `on` handler | ❌ (run-to-completion) | ❌ Compile error |

### Compile-Time Enforcement

```simple
sync fn bad_sync():
    let x ~= fetch()    # ERROR: suspension in sync function

fn good_async():
    let x ~= fetch()    # OK: fn allows suspension

actor Counter:
    on Increment(n: i64) async:
        let x ~= fetch()    # ERROR: actor handlers are run-to-completion
```

### Suspension Propagation

A function that uses `~=`, `if~`, or `while~` is automatically inferred as potentially suspending:

```simple
fn wrapper() -> Data:
    let x ~= inner_fetch()   # wrapper is now suspending
    return x

sync fn caller():
    let d = wrapper()        # ERROR: calling suspending fn from sync
```

---

## Interaction with Existing Constructs

### With `await`

`~=` is syntactic sugar for `await`:

```simple
# These are equivalent:
let x ~= fetch_data()
let x = await fetch_data()

# But ~= allows type-driven behavior:
let x: Data ~= maybe_future()   # Works if maybe_future returns Data or Future[Data]
```

### With `?` Error Propagation

Suspension and error propagation compose:

```simple
fn load_config() -> Result[Config, Error]:
    # Suspend, then propagate error
    let content ~= read_file(path)?

    # Equivalent to:
    let content = await read_file(path)?

    # Or explicitly:
    let future = read_file(path)
    let result = await future
    let content = result?

    return parse(content)
```

**Order of operations:** `~=` first (await), then `?` (propagate error)

### With Pattern Matching

```simple
# Suspending pattern match in while
while~ let Some(msg) = channel.recv():
    handle(msg)

# Suspending match expression
match~ fetch_status():
    case Ready: proceed()
    case Pending: wait()
    case Error(e): fail(e)
```

### With Futures and Combinators

```simple
# Traditional combinator style (still valid)
let result = fetch_a()
    .then(\a: fetch_b(a))
    .then(\b: process(b))
    .catch(\e: handle_error(e))

# With suspension operator (imperative style)
let a ~= fetch_a()
let b ~= fetch_b(a)
let result ~= process(b)
```

---

## Examples

### Basic HTTP Request

```simple
fn get_user(id: UserId) -> Result[User, HttpError]:
    let response ~= http.get("/users/{id}")?
    let user: User ~= response.json()?
    return Ok(user)
```

### Polling Loop

```simple
fn wait_for_ready(timeout: Duration) -> Result[(), TimeoutError]:
    let deadline = now() + timeout

    while~ not is_ready():
        if now() > deadline:
            return Err(TimeoutError("Timed out waiting for ready"))
        _ ~= timer.sleep(100_ms)

    return Ok(())
```

### Parallel Fetch with Sequential Processing

```simple
fn fetch_and_merge(ids: [UserId]) -> [User]:
    # Start all fetches in parallel
    let futures = ids.map(\id: fetch_user(id))

    # Wait for all (suspends once)
    let users ~= Future.all(futures)

    return users
```

### Conditional Async

```simple
fn smart_fetch(id: UserId, use_cache: bool) -> User:
    if use_cache:
        # Non-suspending path
        if let Some(user) = cache.get(id):
            return user

    # Suspending path
    let user ~= fetch_from_server(id)
    cache.set(id, user)
    return user
```

### Stream Processing

```simple
fn process_stream(stream: AsyncStream[Message]) -> Stats:
    let mut stats = Stats.new()

    for~ msg in stream:
        match msg:
            case Data(payload):
                stats.record(payload)
            case Heartbeat:
                _ ~= send_ack()
            case Close:
                break

    return stats
```

### Actor with Async Request-Response

```simple
# Actors cannot use ~ directly, but can spawn futures
actor DataService:
    state:
        cache: Dict[Key, Value] = {}

    on Query(key: Key, reply_to: Pid[Value]) async:
        if key in self.cache:
            send reply_to, self.cache[key]
        else:
            # Spawn async task (not blocking the actor)
            spawn_task:
                let value ~= fetch_remote(key)
                send self, CacheAndReply(key, value, reply_to)

    on CacheAndReply(key: Key, value: Value, reply_to: Pid[Value]) async:
        self.cache[key] = value
        send reply_to, value
```

---

## Compound Suspending Assignment

For modify-and-assign patterns:

```simple
# Suspending compound assignment
counter ~+= fetch_increment()    # counter = counter + (await fetch_increment())

# All compound operators have suspending variants
value ~-= get_decrement()
total ~*= get_multiplier()
quota ~/= get_divisor()
remainder ~%= get_modulo()
```

**Grammar:**
```ebnf
CompoundSuspendOp -> "~+=" | "~-=" | "~*=" | "~/=" | "~%="
```

---

## Chained Suspending Conditions

For complex boolean expressions:

```simple
# Both conditions may suspend
if~ check_auth() and~ has_permission():
    allow()

# First suspends, second is sync
if~ is_online() and is_valid(token):
    proceed()

# Short-circuit: second only evaluated if first is true
if~ expensive_check() and~ another_expensive_check():
    ...
```

**Semantics:**
- `and~` / `or~` mark the right operand as potentially suspending
- Short-circuit evaluation applies: `and~` only evaluates RHS if LHS is true
- `or~` only evaluates RHS if LHS is false

---

## Error Messages

### Suspension in Sync Context

```
error[E0270]: suspension operator `~=` used in sync function
  --> src/main.spl:15:12
   |
14 | sync fn load():
15 |     let x ~= fetch()
   |           ^^ suspension not allowed in `sync fn`
   |
   = help: remove `sync` modifier or use non-suspending alternative
```

### Missing Suspension Marker

```
warning[W0271]: calling suspending function without `~=`
  --> src/main.spl:20:13
   |
20 |     let x = fetch()
   |             ^^^^^^^ `fetch()` returns `Future[Data]`
   |
   = help: use `let x ~= fetch()` to await, or `let x = fetch()` to get the Future
```

### Actor Handler Suspension

```
error[E0272]: suspension not allowed in actor handler
  --> src/actors.spl:8:16
   |
 7 |     on Process(data: Data) async:
 8 |         let x ~= fetch()
   |               ^^ actor handlers must be run-to-completion
   |
   = help: spawn a task instead: `spawn_task: let x ~= fetch(); ...`
```

---

## Implementation Notes

### Desugaring

The compiler desugars `~` constructs to explicit `await`:

```simple
# Source
let x ~= expr

# Desugared
let __tmp = expr
let x = if __tmp is Future:
    await __tmp
else:
    __tmp
```

For guards:

```simple
# Source
if~ cond:
    body

# Desugared
let __cond = cond
let __resolved = if __cond is Future:
    await __cond
else:
    __cond
if __resolved:
    body
```

### MIR Instructions

New MIR instructions for suspension:

| Instruction | Description |
|-------------|-------------|
| `SuspendAssign(dst, src)` | Await `src` if Future, assign to `dst` |
| `SuspendBranch(cond, then_bb, else_bb)` | Await `cond` if Future, branch |
| `SuspendLoop(cond, body_bb, exit_bb)` | Loop with suspending condition |

### Runtime Behavior

1. **Threaded mode:** `~=` schedules await on thread pool, current fiber yields
2. **Manual mode:** `~=` adds to poll queue, returns control to caller
3. **Sync context:** Compile error (never reaches runtime)

---

## Comparison with Other Languages

| Language | Suspension Syntax | Notes |
|----------|-------------------|-------|
| Simple | `~=`, `if~`, `while~` | Explicit, composable |
| JavaScript | `await` keyword | Expression-level only |
| Rust | `.await` postfix | Expression-level only |
| Python | `await` keyword | Expression-level only |
| Kotlin | `suspend` functions | Implicit at call site |
| Swift | `await` keyword | Required at call site |

Simple's `~` operator provides:
- **Statement-level markers** for control flow (unique)
- **Compound assignment** support (`~+=`, etc.)
- **Guard-level suspension** (`if~`, `while~`)

---

## Migration Guide

### From Explicit `await`

```simple
# Before
let x = await fetch()
if await is_ready():
    ...

# After (both valid, choose by preference)
let x ~= fetch()
if~ is_ready():
    ...
```

### From Implicit Await

If your codebase used type-driven implicit await:

```simple
# Before (implicit await when assigning Future to non-Future type)
let x: Data = fetch()   # Implicitly awaited

# After (explicit suspension)
let x: Data ~= fetch()  # Explicitly suspending
```

---

## Feature Flags

| Flag | Description |
|------|-------------|
| `#[warn(missing_suspend)]` | Warn when assigning Future without `~=` |
| `#[deny(implicit_suspend)]` | Error on any implicit suspension |
| `#[allow(implicit_suspend)]` | Allow implicit await (legacy mode) |

---

## Summary

| Syntax | Context | Effect |
|--------|---------|--------|
| `x ~= expr` | Assignment | Await and assign |
| `if~ cond:` | Guard | Suspending condition |
| `while~ cond:` | Guard | Suspending loop condition |
| `for~ x in iter:` | Loop | Async iterator |
| `and~`, `or~` | Boolean | Suspending operand |
| `~+=`, `~-=`, etc. | Compound | Suspending modify-assign |

The `~` operator makes async control flow **explicit, composable, and safe**.

---

## Related Specifications

- [Concurrency](concurrency.md) - Full async/await specification
- [Effects](capability_effects.md) - Effect system details
- [Syntax](syntax.md) - Core language syntax
