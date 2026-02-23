# Borrowing, Purity Inference, and Type System Design

**Date**: 2026-02-07
**Status**: Approved Design
**Related**: `doc/design/memory.md`, `doc/design/val_mut_semantics.md`, `doc/design/type_inference.md`, `doc/report/effect_system_complete_2026-02-03.md`

---

## 1. Overview

Simple uses a **hybrid Koka-style effect inference + explicit `pure fn` + `with`-scoped borrowing** system. Purity is **inferred** by the compiler for all functions (extending the existing async/sync inference). The `pure fn` keyword provides opt-in enforcement. Borrowing uses `with` scoping — borrowed values can only be passed to pure functions, eliminating the need for lifetime annotations. `mu` is added as an alias for `me`.

**New keywords**: `pure` (modifier), `mu` (alias for `me`)
**Extended syntax**: `with x:` (borrow), `with mu x:` (mutable borrow)
**No breaking changes**: `fn` behavior is unchanged.

---

## 2. Design Principles

1. **No breaking changes** — `fn` stays as-is (can be impure)
2. **Infer, don't annotate** — purity detected automatically (Koka-style)
3. **`with` unifies** resource cleanup and borrow scoping
4. **Purity replaces lifetimes** — pure functions can't leak borrows, so no `'a` annotations needed
5. **Gradual adoption** — `pure fn` is opt-in; existing code works unchanged

---

## 3. Keyword Reference

| Keyword | Meaning | New? | Example |
|---------|---------|------|---------|
| `fn` | Function (can be impure) | No | `fn process(data):` |
| `pure fn` | Pure function (compiler verifies no side effects) | **Yes** | `pure fn add(a, b): a + b` |
| `me` | Mutable method (can modify self) | No | `me increment():` |
| `mu` | Alias for `me` | **Yes** | `mu increment():` |
| `with x:` | Immutable borrow scope | **Extended** | `with data:` |
| `with mu x:` | Exclusive mutable borrow scope | **New** | `with mu data:` |

---

## 4. Purity System

### 4.1 `fn` — Unchanged

`fn` behaves exactly as it does today. Free functions can perform I/O, mutate globals, etc. No breaking change.

```simple
fn process(data):
    print data.len()          # Fine — fn can do I/O
    file_write("log", data)   # Fine — fn can do I/O
```

### 4.2 `pure fn` — Opt-in Purity Enforcement

`pure fn` declares that a function has **no side effects**. The compiler verifies this claim.

```simple
pure fn add(a: i64, b: i64) -> i64:
    a + b                     # OK: arithmetic is pure

pure fn square(x: i64) -> i64:
    add(x, x)                # OK: add is pure (inferred)

# pure fn bad():
#     print "hello"           # ERROR: pure fn cannot call impure function 'print'

# pure fn also_bad():
#     GLOBAL = 42             # ERROR: pure fn cannot modify global state
```

**What `pure fn` prohibits:**
- Calling impure functions (I/O, print, file operations)
- Modifying global/module-level variables
- Modifying captured variables (closures)
- Any operation with inferred effect ≠ `total`

### 4.3 Koka-Style Purity Inference

The compiler **infers effects** for ALL functions automatically, extending the existing async/sync inference engine. No annotations required.

```simple
# Compiler infers: total (pure — no effects)
fn add(a, b):
    a + b

# Compiler infers: <console> (has print effect)
fn greet(name):
    print "Hello, {name}"

# Compiler infers: <io> (file I/O effect)
fn save(path, data):
    file_write(path, data)

# Compiler infers: <io, console> (multiple effects)
fn save_and_log(path, data):
    file_write(path, data)       # <io>
    print "Saved to {path}"      # <console>
```

**Effect categories:**

| Effect | Triggered by | Example |
|--------|-------------|---------|
| `total` | No effects (pure) | `fn add(a, b): a + b` |
| `<console>` | `print`, `input` | `fn greet(): print "hi"` |
| `<io>` | File/network I/O | `fn save(): file_write(...)` |
| `<mutation>` | Global/captured var modification | `fn inc(): COUNTER = COUNTER + 1` |
| `<async>` | Suspension operators (`~`) | Already implemented |

### 4.4 Effect Inference Algorithm

Extends the existing fixed-point iteration from `src/compiler/effects_*.spl`:

```
1. Initialize all functions as total (pure)
2. Mark built-in impure functions (print, file_*, process_*, etc.)
3. Repeat until no changes:
   a. For each function, scan body for:
      - Calls to impure functions → propagate their effects
      - Global variable writes → add <mutation>
      - Captured variable writes → add <mutation>
   b. Propagate effects through call graph
4. Return when converged
```

### 4.5 Effect Polymorphism

Higher-order functions inherit the effects of their function arguments:

```simple
fn map(list, f):
    [for x in list: f(x)]
    # Effect of map = effect of f (polymorphic)

# Pure usage:
map([1,2,3], \x: x * 2)           # Inferred: total (pure)

# Impure usage:
map([1,2,3], \x: print x; x)      # Inferred: <console>

# Same function, different effects depending on the argument.
# No need for separate pure_map() and impure_map().
```

### 4.6 `pure fn` as Assertion

`pure fn` is syntactic sugar for asserting `total` effect. The compiler checks:

```simple
pure fn compute(x):       # Assertion: this function must be total
    x * x + 1             # OK: inferred total

pure fn bad(x):            # Assertion: this function must be total
    print x                # ERROR: function has <console> effect,
                           #        but declared pure fn (requires total)
```

---

## 5. `mu` Alias for `me`

`mu` and `me` are **interchangeable** everywhere. Both mean "mutable method."

```simple
class Counter:
    count: i64

    fn get() -> i64:              # Immutable method
        self.count

    me increment():               # Mutable method (me)
        self.count = self.count + 1

    mu decrement():               # Mutable method (mu = same as me)
        self.count = self.count - 1
```

`mu` comes from "mutate" — more universal than `me` (which implies "self"). Use whichever reads better.

---

## 6. Borrowing with `with`

### 6.1 Immutable Borrow: `with x:`

Creates a scope where `x` is borrowed immutably. The original variable is **fully inaccessible** (Rust-style) until the scope ends.

```simple
var data = mut [1, 2, 3]

# Borrow without alias — use same name
with data:
    val len = count(data)       # OK: count is pure
    val first = data[0]         # OK: read access
    # data.push(4)              # ERROR: immutable borrow — cannot mutate
# data is released — full access restored

data.push(4)                    # OK: outside borrow scope

# Borrow with alias
with data as snapshot:
    val len = count(snapshot)   # OK: use alias
    # data.push(4)              # ERROR: original 'data' inaccessible during borrow
    # snapshot.push(4)          # ERROR: immutable borrow — cannot mutate
```

### 6.2 Mutable Borrow: `with mu x:`

Creates a scope where `x` is borrowed exclusively with mutation rights. The original variable is **fully inaccessible** until the scope ends.

```simple
var data = mut [1, 2, 3]

# Mutable borrow without alias
with mu data:
    data.push(4)                # OK: mutation allowed
    data.push(5)                # OK: mutation allowed
    val len = count(data)       # OK: count is pure — can read

# Mutable borrow with alias
with mu data as editor:
    editor.push(6)              # OK: mutation via alias
    val len = count(editor)     # OK: reading via pure fn
    # data[0]                   # ERROR: original 'data' inaccessible
```

### 6.3 Disambiguation from Resource `with`

| Syntax | Meaning | How compiler distinguishes |
|--------|---------|---------------------------|
| `with File.open("x") as f:` | Resource (calls f.close() on exit) | Expression + `as` required |
| `with data:` | Immutable borrow | Bare identifier, no `as` |
| `with data as snap:` | Immutable borrow with alias | Bare identifier + `as` |
| `with mu data:` | Mutable borrow | `mu` keyword after `with` |
| `with mu data as editor:` | Mutable borrow with alias | `mu` keyword + `as` |

**Rule**: If the expression after `with` is a **bare identifier** (not a method call or constructor), it's a borrow. If it's a **complex expression** (call, field access), it's a resource.

```simple
with File.open("x") as f:     # Resource: File.open() is a call expression
with data:                      # Borrow: data is a bare identifier
with mu data:                   # Mutable borrow: mu + bare identifier
with connection as conn:        # Borrow: bare identifier + as
with db.connect() as conn:     # Resource: db.connect() is a call expression
```

### 6.4 Nesting Rules

```simple
var a = mut [1, 2]
var b = mut [3, 4]

# Borrow different variables: OK
with a:
    with b:
        val total = count(a) + count(b)   # OK: both pure

# Borrow same variable twice (immutable): OK
with a:
    with a as a2:          # OK: multiple immutable borrows allowed
        count(a) + count(a2)

# Mutable + any borrow of same variable: ERROR
with mu a:
    # with a:              # ERROR: a is exclusively borrowed by mu
    # with a as x:         # ERROR: same
    pass
```

---

## 7. The Purity-Borrow Rule

**Core rule**: Inside a `with` scope, borrowed values can **only be passed to pure functions** (inferred pure or `pure fn`).

### 7.1 Why This Works

A pure function:
- Cannot store the value in a global → borrow can't escape
- Cannot write to file/network → borrow can't escape
- Cannot modify captured variables → borrow can't escape
- Can only compute and return a derived value → safe

An impure function:
- Could store the reference in a global → borrow escapes scope
- Could send it over a channel → borrow escapes scope
- Could assign it to a longer-lived variable → dangling reference

**Therefore: purity = borrow safety. No lifetime annotations needed.**

### 7.2 Examples

```simple
# Pure functions (inferred)
fn count(items): items.len()              # Inferred: total
fn sum(items):                            # Inferred: total
    var total = 0
    for x in items: total = total + x
    total

# Impure functions (inferred)
fn save(items): file_write("out", items)  # Inferred: <io>
fn log(items): print items                # Inferred: <console>

var data = mut [1, 2, 3]

with data:
    val n = count(data)       # OK: count is pure
    val s = sum(data)         # OK: sum is pure
    # save(data)              # ERROR: save is impure — cannot pass borrow
    # log(data)               # ERROR: log is impure — cannot pass borrow

with mu data:
    data.push(4)              # OK: direct mutation in mu scope
    val n = count(data)       # OK: count is pure
    # save(data)              # ERROR: save is impure
```

### 7.3 `with mu` Scope: Mutation + Pure Reading

In a `with mu` scope, you can:
- **Mutate** the borrowed value directly (push, pop, assign fields, etc.)
- **Pass** to pure functions for reading (count, sum, map with pure lambda, etc.)
- **NOT pass** to impure functions

```simple
with mu data:
    # Direct mutation: OK
    data.push(42)
    data[0] = 99

    # Pass to pure fn for reading: OK
    val len = count(data)
    val doubled = map(data, \x: x * 2)   # OK: lambda is pure

    # Pass to impure fn: ERROR
    # save(data)              # ERROR: impure
    # map(data, \x: print x) # ERROR: lambda is impure (<console>)
```

---

## 8. Lambda Inference

### 8.1 Purity Inference for Lambdas

Lambdas are inferred pure or impure from their body and captures:

```simple
# Pure lambda: no side effects, no mutable captures
val double = \x: x * 2                    # Inferred: total
val add = \a, b: a + b                    # Inferred: total

# Impure lambda: has side effects
val logger = \x: print x                  # Inferred: <console>
val saver = \x: file_write("out", x)      # Inferred: <io>

# Impure lambda: mutates captured variable
var count = 0
val inc = \: count = count + 1             # Inferred: <mutation>
```

### 8.2 Lambda Types

```simple
# Pure lambda type
fn(i64) -> i64                  # A pure function from i64 to i64

# Impure lambda type (mu = can have effects)
mu(i64) -> ()                   # An effectful function from i64 to unit

# Type hierarchy (subtyping):
# fn <: mu
# A pure lambda IS-A mu lambda (can be used where mu is expected)
# A mu lambda is NOT a fn lambda (cannot be used where purity required)
```

### 8.3 Lambdas in Borrow Scopes

```simple
var data = mut [1, 2, 3]

with data:
    # Pure lambda: can receive borrow
    val doubled = map(data, \x: x * 2)    # OK

    # Impure lambda: cannot receive borrow (through map)
    # map(data, \x: print x; x)           # ERROR: lambda is <console>

    # Direct lambda with borrow
    val process = \items: items.len()      # Inferred: total
    process(data)                           # OK: pure

with mu data:
    # Pure lambda for reading: OK
    val filtered = filter(data, \x: x > 2)  # OK: lambda is total

    # Mutation via method calls: OK
    data.push(42)
```

---

## 9. Cross-Language Research

### 9.1 Purity Comparison

| Language | Purity Approach | Simple's Approach |
|----------|----------------|-------------------|
| **Haskell** | Default pure, IO monad for effects | Inferred (Koka-style), `pure fn` for opt-in |
| **Koka** | Inferred effects, row-polymorphic | **Same** — extends existing async/sync inference |
| **Rust** | No purity tracking (`const fn` limited) | More granular — tracks IO, mutation, console |
| **Swift** | `mutating` on value types only | `fn`/`me`(`mu`) + inferred effects on all |
| **C#** | `readonly` on struct methods | Broader — applies to all functions |

### 9.2 Borrowing Comparison

| Language | Borrowing | Lifetime Annotations | Simple's Approach |
|----------|-----------|---------------------|-------------------|
| **Rust** | `&T`/`&mut T` everywhere | Yes (`'a`) | `with` scoped, no annotations |
| **Swift 5.9** | `borrowing`/`consuming` params | No | `with`/`with mu` scoping |
| **C#** | `ref`/`in`/`scoped` params | `scoped` keyword | `with` scoping |
| **Koka** | Effect handlers | No | Purity = safety |

### 9.3 Key Insight: Simple's Novel Contribution

**No other language uses purity as the mechanism for borrow safety.** This is Simple's novel approach:

- **Rust**: Uses lifetime annotations (`'a`) to prove borrows don't escape — complex
- **Swift**: Uses Law of Exclusivity (runtime checks for some cases) — incomplete
- **Simple**: Uses purity inference — pure functions provably can't escape borrows — elegant

---

## 10. Phased Implementation

| Phase | What | Effort | Depends On |
|-------|------|--------|------------|
| 1 | Purity inference engine (extend async/sync fixed-point) | 12-16h | Existing effect system |
| 2 | `pure fn` syntax + compiler verification | 8-12h | Phase 1 |
| 3 | `mu` alias for `me` (parser change) | 2-4h | None |
| 4 | `with x:` / `with mu x:` borrow scoping | 12-16h | Phase 1 |
| 5 | Purity-borrow rule enforcement | 8-12h | Phase 1 + Phase 4 |
| 6 | Lambda purity inference | 8-12h | Phase 1 |
| **Total** | | **50-72h** | |

### Phase 1: Purity Inference Engine (12-16h)

Extend `src/compiler/effects_*.spl` to track more than async/sync:

```
Current:  Effect = Sync | Async
Extended: Effect = { async: bool, io: bool, console: bool, mutation: bool }
          total = all false
```

- Reuse existing fixed-point iteration algorithm
- Add impurity sources: `print` → console, `file_*` → io, global write → mutation
- Propagate through call graph (already implemented for async)

### Phase 2: `pure fn` Syntax (8-12h)

- Add `pure` as context-sensitive keyword (only before `fn`)
- After effect inference, check: if `pure fn`, assert effect = total
- Emit error with specific effect that violates purity

### Phase 3: `mu` Alias (2-4h)

- Parser: accept `mu` wherever `me` is accepted
- AST: both map to same node type
- No semantic changes

### Phase 4: `with` Borrow Scoping (12-16h)

- Parser: `with IDENT:` and `with mu IDENT:` and variants with `as`
- Disambiguate from resource `with` (bare identifier vs expression)
- Scope tracking: mark variable as borrowed, block access to original
- On scope exit: release borrow

### Phase 5: Purity-Borrow Rule (8-12h)

- At each function call inside `with` scope:
  - Look up callee's inferred effect
  - If not total → ERROR: "cannot pass borrowed value to impure function"
- At each mutation inside `with` (non-mu) scope → ERROR
- At each mutation inside `with mu` scope → OK

### Phase 6: Lambda Purity Inference (8-12h)

- Infer lambda effects from body (same as function inference)
- Track captures: mutable capture → `<mutation>` effect
- Check lambda compatibility at call sites

---

## 11. Lean Verification

### 11.1 Purity Inference Soundness

**Goal**: Prove that if the compiler infers a function as `total` (pure), it truly has no observable side effects.

**Proof obligations:**

1. **Effect Propagation Completeness**: If function `f` calls function `g` with effect `E`, then `f` must have effect `E` (or superset).

   ```lean
   theorem effect_propagation_complete :
     ∀ f g E, calls f g → has_effect g E → has_effect f E
   ```

2. **Fixed-Point Convergence**: The effect inference algorithm always terminates and produces a unique fixed point.

   ```lean
   theorem inference_converges :
     ∀ program, ∃ n, iterate n program = iterate (n + 1) program
   ```

3. **Total Means No Effects**: A function inferred as `total` performs no I/O, no mutation, no console output.

   ```lean
   theorem total_is_pure :
     ∀ f, inferred_effect f = total →
       ¬ (performs_io f ∨ performs_mutation f ∨ performs_console f)
   ```

### 11.2 Borrow Safety via Purity

**Goal**: Prove that borrowed values cannot escape their `with` scope when only passed to pure functions.

**Proof obligations:**

4. **No Escape Through Pure Functions**: A pure function cannot store its argument in any location that outlives the function call.

   ```lean
   theorem pure_no_escape :
     ∀ f arg, is_total f → calls_with f arg →
       ¬ (∃ loc, stored_at loc arg ∧ outlives loc (scope_of f))
   ```

5. **Borrow Scope Exclusivity**: During a `with mu` scope, no other reference to the variable can be accessed.

   ```lean
   theorem mu_borrow_exclusive :
     ∀ x scope, is_mu_borrow scope x →
       ¬ (∃ ref, ref ≠ scope.binding ∧ accesses ref x ∧ within scope ref)
   ```

6. **Borrow Release Correctness**: After `with` scope ends, the original variable is fully accessible again.

   ```lean
   theorem borrow_release :
     ∀ x scope, is_borrow scope x → after scope →
       accessible x ∧ mutable x
   ```

### 11.3 Purity-Borrow Interaction

7. **Borrow Passing Soundness**: If a borrowed value is passed only to pure functions within a `with` scope, no dangling references exist after scope exit.

   ```lean
   theorem borrow_passing_sound :
     ∀ x scope, is_borrow scope x →
       (∀ f, called_with f x → within scope → is_total f) →
       after scope → no_dangling_refs x
   ```

### 11.4 Verification Files

| File | Proves |
|------|--------|
| `verification/purity/effect_propagation.lean` | Obligation 1 |
| `verification/purity/fixed_point.lean` | Obligation 2 |
| `verification/purity/total_soundness.lean` | Obligation 3 |
| `verification/borrow/no_escape.lean` | Obligation 4 |
| `verification/borrow/exclusivity.lean` | Obligation 5 |
| `verification/borrow/release.lean` | Obligation 6 |
| `verification/borrow/passing_sound.lean` | Obligation 7 |

---

## 12. Comprehensive Examples

### 12.1 Basic Purity

```simple
# Inferred pure (total)
fn distance(x1, y1, x2, y2):
    val dx = x2 - x1
    val dy = y2 - y1
    (dx * dx + dy * dy).sqrt()

# Inferred impure (<console>)
fn log_distance(x1, y1, x2, y2):
    val d = distance(x1, y1, x2, y2)   # OK: calling pure from impure
    print "Distance: {d}"

# Explicit pure (compiler verifies)
pure fn midpoint(x1, y1, x2, y2):
    ((x1 + x2) / 2, (y1 + y2) / 2)
```

### 12.2 Borrowing with `with`

```simple
var players = mut [
    Player(name: "Alice", hp: 100),
    Player(name: "Bob", hp: 80),
]

# Read-only borrow
with players:
    val alive = count_alive(players)     # OK: count_alive is pure
    val names = map(players, \p: p.name) # OK: lambda is pure
    print_stats(players)                 # ERROR: print_stats is impure (<console>)

# Use alias for clarity
with players as roster:
    val total = sum(map(roster, \p: p.hp))  # OK: all pure
    # players.push(...)                      # ERROR: players inaccessible

# Mutable borrow
with mu players:
    players.push(Player(name: "Charlie", hp: 90))  # OK: mutation
    val n = players.len()                           # OK: len is pure
    # save_players(players)                         # ERROR: save is impure

# After all borrows: full access
save_players(players)                    # OK: not borrowed
```

### 12.3 Effect Polymorphism

```simple
fn map(list, f):
    [for x in list: f(x)]

fn filter(list, pred):
    [for x in list if pred(x): x]

fn fold(list, init, f):
    var acc = init
    for x in list: acc = f(acc, x)
    acc

# All three are effect-polymorphic:
# Their effect = effect of the function argument

var data = mut [1, 2, 3, 4, 5]

with data:
    # Pure lambdas → map/filter/fold are total → OK with borrow
    val doubled = map(data, \x: x * 2)
    val evens = filter(data, \x: x % 2 == 0)
    val total = fold(data, 0, \acc, x: acc + x)

    # Impure lambda → map becomes <console> → ERROR with borrow
    # map(data, \x: print x; x)
```

### 12.4 Classes with `mu`

```simple
class GameState:
    players: mut [Player]
    score: i64
    round: i64

    fn get_score() -> i64:        # Immutable method
        self.score

    fn is_over() -> bool:         # Immutable method
        self.round > 10

    mu next_round():              # Mutable method (mu = me)
        self.round = self.round + 1

    mu add_player(p: Player):     # Mutable method
        self.players.push(p)

pure fn total_hp(state: GameState) -> i64:
    fold(state.players, 0, \acc, p: acc + p.hp)

# Borrow the game state
var game = GameState(players: mut [], score: 0, round: 1)

with game:
    val hp = total_hp(game)       # OK: total_hp is pure fn
    val over = game.is_over()     # OK: fn method is pure
    # game.next_round()           # ERROR: mu method in immutable borrow

with mu game:
    game.next_round()             # OK: mu method in mu borrow
    game.add_player(Player(name: "Alice", hp: 100))  # OK
    val hp = total_hp(game)       # OK: reading via pure fn
```

### 12.5 Lambda Types in Function Signatures

```simple
# Accept only pure function
fn apply_pure(f: fn(i64) -> i64, x: i64) -> i64:
    f(x)

# Accept any function (pure or impure)
fn apply(f: mu(i64) -> i64, x: i64) -> i64:
    f(x)

val double = \x: x * 2          # Inferred: fn (pure)
val log_and_double = \x:         # Inferred: mu (impure — console)
    print x
    x * 2

apply_pure(double, 5)            # OK: pure lambda → fn parameter
apply_pure(log_and_double, 5)    # ERROR: impure lambda → fn parameter

apply(double, 5)                  # OK: pure is subtype of mu
apply(log_and_double, 5)          # OK: impure lambda → mu parameter
```
