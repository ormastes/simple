# Go Goroutines vs Simple Isolated Threads

## Research Comparison & Improvement Proposals

**Status:** Research
**Date:** 2026-01-16

---

## Simple's Core Rules (Non-Negotiable)

| Rule | Description |
|------|-------------|
| **No shared mutable state** | Cannot access mutable globals from threads |
| **Copy or const only** | Data must be deep-copied or immutable |
| **Channel-only communication** | Channels are the only inter-thread mechanism |
| **Global const access** | Can read global constants |

These rules **prevent data races by design** - stronger than Go's approach.

---

## Side-by-Side Comparison

### 1. Thread Spawning

**Go:**
```go
// Implicit capture - can cause data races
go func() {
    fmt.Println(data)  // data captured by reference!
}()
```

**Simple (Current):**
```simple
# Explicit copy - safe by design
val handle = spawn_isolated(data) \copied_data:
    print(copied_data)  # copied_data is deep copy
```

**Analysis:** Simple is safer but more verbose.

---

### 2. Channel Operations

**Go:**
```go
ch := make(chan int)
ch <- 42       // send
x := <-ch      // receive
close(ch)
```

**Simple (Current):**
```simple
val ch = Channel.new()
ch.send(42)
val x = ch.recv()
ch.close()
```

**Simple (Proposed with `<-` operator):**
```simple
val ch = Channel.new()
ch <- 42           # send (infix operator)
val x = <-ch       # receive (prefix operator)
ch.close()
```

**Analysis:** Add `<-` as syntactic sugar for `send`/`recv`.

---

### 3. Select/Multiplexing

**Go:**
```go
select {
case v := <-ch1:
    handle(v)
case ch2 <- x:
    // sent
case <-time.After(time.Second):
    // timeout
default:
    // non-blocking
}
```

**Simple (Current):** No equivalent.

---

### 4. Cancellation

**Go:**
```go
ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
defer cancel()
go func(ctx context.Context) {
    select {
    case <-ctx.Done():
        return
    case result := <-work():
        process(result)
    }
}(ctx)
```

**Simple (Current):** No equivalent.

---

## Proposed Improvements (Simple-Compatible)

### Proposal 1: `go` Keyword with Two Styles

Keep safety, reduce verbosity:

```simple
# Current
val handle = spawn_isolated(data) \d: d.sum()

# Style A: Rust-style capture with pipes (LL(1) safe)
val handle = go |data| \: data.sum()

# Multiple captures (all deep-copied)
val handle = go |data, config| \: process(data, config)

# With channel (channel refs are safe to share)
val handle = go |data, ch| \: ch.send(data.sum())

# Style B: Current style with 'go' keyword (LL(1) safe)
val handle = go(data) \d: d.sum()

# With multiple args
val handle = go(data, ch) \d, c: c.send(d.sum())
```

**Rules:**
- Style A: `go |captures| \: expr` - Rust-style pipes, captures auto-copied
- Style B: `go(args) \params: expr` - like current `spawn_isolated`
- All captured/passed values are deep-copied (except channels)
- Channels use reference semantics (safe - they're sync primitives)
- Both styles are **LL(1) compatible**

---

### Proposal 2: Channel Direction Types + `<-` Operator

Prevent misuse at compile time with wrapper types:

```simple
# Type-safe channel directions (wrapper types)
struct Sender<T>:
    _ch: Channel<T>

    fn send(value: T):
        self._ch.send(value)

    # Support <- operator for send
    operator <-(value: T):
        self.send(value)

struct Receiver<T>:
    _ch: Channel<T>

    fn recv() -> Option<T>:
        self._ch.recv()

    # Support prefix <- operator for receive
    prefix operator <-() -> Option<T>:
        self.recv()

# Usage
fn producer(out: Sender<i32>):
    out <- 42          # send via operator
    out.send(42)       # or method call
    # out.recv()       # Compile error! No recv on Sender

fn consumer(inp: Receiver<i32>):
    val v = <-inp      # receive via operator
    val w = inp.recv() # or method call
    # inp.send(1)      # Compile error! No send on Receiver

# Create typed pair
fn typed_channel<T>() -> (Sender<T>, Receiver<T>):
    val ch = Channel.new()
    return (Sender(_ch: ch), Receiver(_ch: ch))

# Example usage
val (tx, rx) = typed_channel<i32>()
go [tx] \: tx <- 42
val result = <-rx
```

---

### Proposal 3: Select Statement

Multi-channel waiting with Simple syntax:

```simple
# Proposed select syntax
select:
    recv rx1 as v:
        handle(v)
    send tx, value:
        # sent successfully
    timeout 1000:
        # 1 second timeout
    default:
        # non-blocking check

# Alternative: using <- operator
select:
    <-rx1 as v:
        handle(v)
    tx <- value:
        # sent
    timeout 1000:
        # timeout

# Implementation: SelectResult enum
enum SelectResult<A, B>:
    First(A)
    Second(B)
    Timeout
    Closed

# Helper function for 2-channel select
fn select2<A, B>(rx1: Receiver<A>, rx2: Receiver<B>, timeout_ms: i64) -> SelectResult<A, B>:
    # ... FFI implementation
    pass
```

**Simple-Compatible Design:**
- No shared state - just waiting on channels
- Channels already handle synchronization
- Values received are copies (immutable)

---

### Proposal 4: Cancellation Token

Cooperative cancellation without shared mutable state:

```simple
# CancelToken is immutable once created
# Uses atomic flag internally (safe primitive)
struct CancelToken:
    _flag: AtomicBool

    static fn new() -> CancelToken:
        CancelToken(_flag: AtomicBool.new(false))

    fn is_cancelled() -> bool:
        self._flag.load(Ordering.Acquire)

    fn cancel():
        self._flag.store(true, Ordering.Release)

# CancelScope provides timeout functionality
struct CancelScope:
    token: CancelToken

    static fn with_timeout(ms: i64) -> CancelScope:
        val token = CancelToken.new()
        # Spawn background timer
        go [token, ms] \:
            sleep(ms)
            token.cancel()
        CancelScope(token: token)

    fn is_done() -> bool:
        self.token.is_cancelled()

# Usage
val scope = CancelScope.with_timeout(5000)
val result_ch = typed_channel<Result<i32>>().1
val handle = go(data, scope, result_ch) \d, s, ch:
    for item in d:
        if s.is_done():
            ch <- Result.Cancelled
            return
        ch <- Result.Ok(process(item))
```

**Why this is safe:**
- `AtomicBool` is a synchronization primitive (like channels)
- Token is passed by copy, but atomic ops work across copies
- No mutable shared state - just atomic flag reads

---

### Proposal 5: WaitGroup Pattern

Document existing primitives as WaitGroup:

```simple
# Using Latch (already exists in stdlib)
fn wait_group_example():
    val n = 10
    val latch = Latch.new(n)
    val (tx, rx) = typed_channel<i32>()

    for i in range(n):
        go(i, latch, tx) \idx, l, ch:
            ch <- compute(idx)
            l.countdown()

    latch.wait()  # Blocks until all done

    # Collect results
    val collected = []
    for _ in range(n):
        collected.push((<-rx).unwrap())
    return collected

# Or define WaitGroup as alias
type WaitGroup = Latch

impl WaitGroup:
    static fn new(count: i64) -> WaitGroup:
        Latch.new(count)

    fn done():
        self.countdown()

    fn wait():
        self.wait()
```

---

### Proposal 6: Parallel Iterators (Ruby-style Chaining)

Higher-level API built on isolated threads, using Ruby-style method chaining:

```simple
# Current
val results = parallel_map(items, \x: x * 2, 4)

# Proposed: Ruby-style method chaining (like items.map in container spec)
val results = items
    .par()                    # Convert to parallel iterator
    .map \x: x * 2            # Ruby-style block syntax
    .filter \x: x > 10
    .collect()

# Or with explicit parens
val results = items.par().map(\x: x * 2).filter(\x: x > 10).collect()

# Implementation
struct ParIter<T>:
    items: List<T>
    num_threads: i64

    static fn from(items: List<T>) -> ParIter<T>:
        ParIter(items: items, num_threads: available_parallelism())

    fn threads(n: i64) -> ParIter<T>:
        ParIter(items: self.items, num_threads: n)

    fn map<R>(f: fn(T) -> R) -> ParIter<R>:
        val results = parallel_map(self.items, f, self.num_threads)
        ParIter(items: results, num_threads: self.num_threads)

    fn filter(pred: fn(T) -> bool) -> ParIter<T>:
        # Filter in parallel, then flatten
        val results = parallel_map(self.items, \x:
            if pred(x): [x] else: []
        , self.num_threads)
        ParIter(items: results.flatten(), num_threads: self.num_threads)

    fn reduce<R>(f: fn(R, T) -> R, init: R) -> R:
        parallel_reduce(self.items, f, init, self.num_threads)

    fn collect() -> List<T>:
        self.items

# Extension method on List (container spec style)
impl List<T>:
    fn par() -> ParIter<T>:
        ParIter.from(self)

# Usage examples
val doubled = [1, 2, 3, 4].par().map \x: x * 2    # [2, 4, 6, 8]
val sum = [1, 2, 3, 4].par().reduce(\a, b: a + b, 0)  # 10

# With thread control
val results = data.par().threads(8).map \x: heavy_compute(x)
```

---

## Summary: Go vs Simple After Improvements

| Feature | Go | Simple (Current) | Simple (Proposed) |
|---------|-----|------------------|-------------------|
| Spawn | `go func(){}` | `spawn_isolated(d) \x: ...` | `go \|d\| \: ...` or `go(d) \x: ...` |
| Channel send | `ch <- v` | `ch.send(v)` | `ch.send(v)` (keep method) |
| Channel recv | `<-ch` | `ch.recv()` | `ch.recv()` or `<-ch` |
| Select | `select {...}` | - | `select: recv ch as v: ...` |
| Cancel | `context.Context` | - | `CancelScope` |
| WaitGroup | `sync.WaitGroup` | `Latch` | `WaitGroup` alias |
| Parallel iter | - | `parallel_map` | `items.par().map \x: ...` |
| **Safety** | Runtime races possible | **Compile-time safe** | **Compile-time safe** |
| **LL(1)** | N/A | ✅ | ✅ (all proposed syntax) |

---

## Key Insight: Simple's Advantage

Go allows this (data race):
```go
var counter int
for i := 0; i < 100; i++ {
    go func() {
        counter++  // RACE CONDITION!
    }()
}
```

Simple **cannot express this** - the rules prevent it:
```simple
var counter = 0
for i in range(100):
    go |counter| \:      # counter is COPIED (pipe syntax, LL(1) safe)
        counter += 1     # modifies local copy only
# counter is still 0 - no race, but also no effect!

# Correct Simple way:
val (tx, rx) = typed_channel<i32>()
for i in range(100):
    go(tx) \t:
        t.send(1)
# Collect
var counter = 0
for _ in range(100):
    counter += rx.recv().unwrap()
```

**Simple trades convenience for safety** - the improvements above reduce verbosity while keeping safety.

---

## LL(1) Parsing Analysis

### Summary

| Syntax | LL(1) Safe? | Issue | Solution |
|--------|-------------|-------|----------|
| `go [captures] \: ...` | ⚠️ No | `[` ambiguous with array | Use `go capture(...)` |
| `go(args) \params: ...` | ✅ Yes | None | Keep as-is |
| `ch <- v` (send) | ⚠️ No | `<-` conflicts with `<` then `-` | Single token `<-` |
| `<-ch` (recv) | ✅ Yes | Prefix unary, unambiguous | Keep as-is |
| `select:` | ✅ Yes | Keyword starts block | Keep as-is |
| `items.par().map \x:` | ✅ Yes | Method chain + lambda | Keep as-is |

---

### Issue 1: `go [captures]` vs Array Literal

**Problem:**
```simple
go [data] \: ...     # Is [data] a capture list or array?
val x = [1, 2, 3]    # Array literal
```

Parser sees `go` then `[` - can't tell if array or capture list with 1 lookahead.

**Solutions:**

```simple
# Solution A: Different bracket (like Rust closures)
go |data| \: data.sum()
go |data, ch| \: ch <- data.sum()

# Solution B: Keyword + parens
go capture(data) \: data.sum()
go capture(data, ch) \: ch <- data.sum()

# Solution C: Just use Style B (already LL(1))
go(data) \d: d.sum()
go(data, ch) \d, c: c <- d.sum()
```

**Recommendation:** Use `|...|` (Rust-style) or drop Style A entirely.

---

### Issue 2: `<-` Operator Tokenization

**Problem:**
```simple
ch <- 42      # send: is this < - 42 or <- 42?
val x = a<-b  # comparison a < (-b) or channel send?
```

**Solution:** Lexer must tokenize `<-` as single token (like Go).

```
# Lexer rules (priority order)
<-    → ARROW_LEFT (channel op)
<     → LT (less than)
-     → MINUS
```

**Spacing rule:** `ch <- v` (spaces) vs `a<b` (no space = comparison)

Or simpler: **require spaces around `<-`** for channel ops.

---

### Issue 3: Prefix `<-` (receive)

**LL(1) Safe:** ✅ Yes

```simple
val v = <-ch    # Prefix unary operator, unambiguous
```

Parser sees `<-` token at expression start → must be receive.

---

### Issue 4: `select:` Statement

**LL(1) Safe:** ✅ Yes

```simple
select:
    recv rx as v:    # 'recv' keyword disambiguates
        handle(v)
    send tx, val:    # 'send' keyword disambiguates
        pass
    timeout 1000:    # 'timeout' keyword
        pass
    default:         # 'default' keyword
        pass
```

Each branch starts with unique keyword → LL(1) compatible.

---

### Issue 5: Lambda After Method Chain

**LL(1) Safe:** ✅ Yes

```simple
items.par().map \x: x * 2
```

- `.map` is method call
- `\x:` starts lambda (backslash is unambiguous)
- No conflict

---

### Revised Syntax Proposal (LL(1) Compatible)

```simple
# Style A: Rust-style capture with pipes (LL(1) safe)
go |data| \: data.sum()
go |data, ch| \: ch <- data.sum()

# Style B: Current spawn style (LL(1) safe)
go(data) \d: d.sum()
go(data, ch) \d, c: c <- d.sum()

# Channel operators (require lexer change)
ch <- 42         # send (single <- token)
val v = <-ch     # receive (prefix <- token)

# Or keep method style (no lexer change needed)
ch.send(42)
val v = ch.recv()
```

---

### Final Recommendation

| Feature | Recommended Syntax | LL(1) |
|---------|-------------------|-------|
| Spawn (capture) | `go \|data\| \: ...` or just use Style B | ✅ |
| Spawn (params) | `go(data) \d: ...` | ✅ |
| Channel send | `ch.send(v)` (keep method) | ✅ |
| Channel recv | `ch.recv()` or `<-ch` | ✅ |
| Select | `select: recv/send/timeout/default` | ✅ |
| Parallel | `items.par().map \x: ...` | ✅ |

**Safest path:** Keep `ch.send()`/`ch.recv()` methods, add `<-` only as optional prefix for receive.

---

## Tooling Interoperability Analysis

### Can `<-` Work with Tree-sitter/LSP/etc?

**Short answer: Yes, with proper implementation.**

### Precedent: Existing Multi-char Operators

Simple already handles similar operators:
```
->    TokenKind::Arrow       (return type)
<=    TokenKind::LtEq        (comparison)
>=    TokenKind::GtEq        (comparison)
<<    TokenKind::ShiftLeft   (bitwise)
>>    TokenKind::ShiftRight  (bitwise)
**    TokenKind::DoubleStar  (power)
```

Adding `<-` follows the same pattern.

### Tree-sitter Compatibility

| Concern | Issue | Solution |
|---------|-------|----------|
| Token definition | Need single `<-` token | Add to grammar: `"<-" @operator.channel` |
| Incremental parsing | `<` then `-` typed | Tree-sitter re-lexes on edit (normal) |
| Syntax highlighting | Must highlight as one | Add `"<-"` to operator list in highlights.scm |
| Error recovery | Partial `<` typed | Standard error node, recovers on next char |

**Tree-sitter grammar addition:**
```javascript
// grammar.js
channel_arrow: $ => '<-',

// In operator rules
operators: $ => choice(
  ...
  $.channel_arrow,  // Must be before '<'
  '<',
  '-',
  ...
)
```

**Highlights.scm addition:**
```scheme
; Channel operators
["<-"] @operator.channel
```

### LSP/IDE Compatibility

| Feature | Impact | Notes |
|---------|--------|-------|
| Auto-complete | None | `<-` completes as operator |
| Go-to-definition | Works | Parser sees Send/Recv nodes |
| Hover info | Works | Can show channel type info |
| Rename | Works | Channel variable rename |
| Semantic tokens | Add new token type | `channel_operator` |

### Potential Issues

| Issue | Severity | Mitigation |
|-------|----------|------------|
| `a<-b` vs `a < -b` | Medium | Lexer: `<-` always wins, use space for `a < -b` |
| Copy-paste from Go | None | Same syntax, works |
| Regex search tools | Low | Search `<-` as literal |
| Syntax highlighters | Low | Update grammar files |

### Languages Using `<-` Successfully

| Language | Use | Tooling Status |
|----------|-----|----------------|
| **Go** | Channel send/recv | Tree-sitter ✅, LSP ✅, all IDEs ✅ |
| **R** | Assignment | Tree-sitter ✅, RStudio ✅ |
| **Haskell** | Do-notation | Tree-sitter ✅, HLS ✅ |
| **OCaml** | Reference assign | Tree-sitter ✅, Merlin ✅ |

**Go's tree-sitter grammar handles `<-` perfectly** - we can copy their approach.

### Implementation Checklist

1. **Lexer** (Rust)
   ```rust
   // In lexer.rs - add before '<' case
   '<' if self.peek() == Some('-') => {
       self.advance(); // consume '-'
       TokenKind::ChannelArrow
   }
   ```

2. **Tree-sitter grammar**
   ```javascript
   channel_send: $ => prec.left(1, seq(
     field('channel', $.expression),
     '<-',
     field('value', $.expression)
   )),

   channel_recv: $ => prec(PREC.PREFIX, seq(
     '<-',
     field('channel', $.expression)
   )),
   ```

3. **Highlights.scm**
   ```scheme
   ["<-"] @operator.channel
   ```

4. **LSP semantic tokens**
   ```rust
   SemanticTokenType::OPERATOR // for <-
   ```

### Conclusion

**`<-` is fully compatible with all standard tooling.** Go has proven this works. The implementation is straightforward:

1. Add `<-` as single lexer token (highest priority)
2. Update tree-sitter grammar
3. Update syntax highlighting
4. Parser handles prefix (recv) vs infix (send) by position

**Risk level: Low** - well-established pattern across multiple languages.

---

## Implementation Priority

| Priority | Feature | Effort | LL(1) | Value |
|----------|---------|--------|-------|-------|
| P1 | `Sender<T>`/`Receiver<T>` wrappers | Low | ✅ | Compile-time safety |
| P1 | Document WaitGroup = Latch | Docs | ✅ | User education |
| P2 | `go` keyword + `\|captures\|` syntax | Medium | ✅ | Developer experience |
| P2 | `go(args) \params:` syntax | Low | ✅ | Simpler alternative |
| P2 | `<-` prefix for recv only | Low | ✅ | Go-like ergonomics |
| P2 | CancelScope/CancelToken | Medium | ✅ | Real-world needs |
| P2 | `items.par().map \x:` style | Medium | ✅ | Ruby-like ergonomics |
| P3 | Select statement | High | ✅ | Complex but powerful |

**Note:** `ch <- v` (infix send) deferred - lexer ambiguity. Keep `ch.send(v)` method.

---

## Quick Reference (LL(1) Safe)

```simple
# Two spawn styles (both copy data, safe, LL(1) compatible)
go |data, ch| \: ch.send(data.sum())     # Style A: pipe capture (Rust-style)
go(data, ch) \d, c: c.send(d.sum())      # Style B: explicit params

# Channel with direction types
val (tx, rx) = typed_channel<i32>()
tx.send(42)                               # send (method)
val v = rx.recv()                         # receive (method)
val w = <-rx                              # receive (prefix op, optional)

# Parallel iteration (Ruby-style)
val results = items.par().map \x: x * 2

# WaitGroup pattern
val latch = Latch.new(n)
go(latch) \l: work(); l.countdown()
latch.wait()

# Cancellation
val scope = CancelScope.with_timeout(5000)
go(scope) \s: while not s.is_done(): work()
```

---

## Implementation Plan

### Phase 1: Foundation (P1 - Low Effort)

| Task | Files | Effort |
|------|-------|--------|
| Add `Sender<T>` wrapper | `std_lib/src/concurrency/channels.spl` | 1 day |
| Add `Receiver<T>` wrapper | `std_lib/src/concurrency/channels.spl` | 1 day |
| Add `typed_channel<T>()` | `std_lib/src/concurrency/channels.spl` | 0.5 day |
| Document WaitGroup = Latch | `doc/guide/concurrency.md` | 0.5 day |
| Create SSpec tests | `std_lib/test/features/` | 1 day |

### Phase 2: Syntax (P2 - Medium Effort)

| Task | Files | Effort |
|------|-------|--------|
| Add `<-` token to lexer | `src/parser/src/lexer.rs` | 0.5 day |
| Add `ChannelArrow` TokenKind | `src/parser/src/token.rs` | 0.5 day |
| Parse prefix `<-expr` (recv) | `src/parser/src/parser_expr.rs` | 1 day |
| Update tree-sitter grammar | `std_lib/src/parser/treesitter/` | 0.5 day |
| Update highlights.scm | `std_lib/src/parser/treesitter/queries/` | 0.5 day |

### Phase 3: Go Keyword (P2 - Medium Effort)

| Task | Files | Effort |
|------|-------|--------|
| Add `go` keyword to lexer | `src/parser/src/lexer.rs` | 0.5 day |
| Parse `go(args) \params: expr` | `src/parser/src/parser_stmt.rs` | 1 day |
| Parse `go \|captures\| \: expr` | `src/parser/src/parser_stmt.rs` | 1 day |
| Lower to `spawn_isolated` call | `src/compiler/src/hir_lower.rs` | 1 day |
| Add SSpec tests | `std_lib/test/features/` | 0.5 day |

### Phase 4: Advanced (P2-P3)

| Task | Files | Effort |
|------|-------|--------|
| `CancelToken` struct | `std_lib/src/concurrency/cancel.spl` | 1 day |
| `CancelScope` struct | `std_lib/src/concurrency/cancel.spl` | 1 day |
| `par()` iterator method | `std_lib/src/collections/list.spl` | 2 days |
| `select` statement (P3) | Multiple parser/compiler files | 3-5 days |

### Phase 5: Documentation

| Task | Location |
|------|----------|
| Concurrency guide | `doc/guide/concurrency.md` |
| Channel patterns | `doc/guide/channel_patterns.md` |
| Migration guide | `doc/migration/go_style_threads.md` |

---

## SSpec Test Files

Feature specifications to create:

| File | Coverage |
|------|----------|
| `concurrency_spec.spl` | `go` keyword, spawn, join |
| `channels_spec.spl` | `Sender`/`Receiver`, `<-` operator |
| `parallel_spec.spl` | `par()`, `parallel_map`, `parallel_reduce` |

---

## References

- Go Concurrency Patterns: https://go.dev/blog/pipelines
- Rust Rayon: https://docs.rs/rayon
- Simple stdlib: `simple/std_lib/src/concurrency/`
- Simple sync primitives: `simple/std_lib/src/infra/sync.spl`
