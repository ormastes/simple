# Simple Language Memory and Ownership

> **📤 EXTRACTED:** Test cases have been extracted to an executable test file:  
> **→** `tests/specs/memory_spec.spl`  
> **Date:** 2026-01-09  
> **Type:** Category B (Extract + Keep)
> 
> This file remains as **architectural reference documentation**.  
> Test cases and examples are in the _spec.spl file for execution and validation.

This document covers memory management, ownership semantics, pointer types, and borrowing.

## Overview

Simple has two memory worlds:

1. **GC-managed references** - plain `T`
2. **Manual/explicit memory** - via pointer types and typed `new` forms

GC is the default; manual memory is opt-in and always explicit in the types. This design allows Simple to be used for both high-level application code (using GC) and performance-critical systems code (using manual memory management) within the same program.

---

## Reference and Pointer Kinds

### GC-Managed Reference: `T`

A bare type `T` is a GC-managed reference to a heap object:

```simple
let p: Player = Player(name: "Hero", hp: 100)
```

Lifetime is fully managed by the garbage collector. This is the default and recommended approach for most code.

### Unique Pointer: `&T`

`&T` is a unique owning pointer:

- Exactly one owner at a time
- Move-only (cannot be copied)
- When the `&T` goes out of scope, the object is destroyed and memory freed (RAII)

```simple
let u: &Player = new(&) Player(name: "Solo", hp: 50)
# u is the sole owner

let v = move u    # ownership transferred to v
# u is now unusable (compile error if accessed)
```

### Shared Pointer: `*T`

`*T` is a shared owning pointer (reference-counted):

- Multiple owners allowed
- Copying/cloning increments the reference count
- Object freed when reference count hits zero

```simple
let s1: *Player = new* Player(name: "Shared", hp: 75)
let s2 = s1       # refcount incremented, both own the object
# Object freed when both s1 and s2 go out of scope
```

### Weak Pointer: `-T`

`-T` is a weak pointer:

- Non-owning reference to an object managed by `*T` (or GC)
- Does not keep the object alive
- Must be upgraded to a strong pointer before use

```simple
let s: *Player = new* Player(name: "Target", hp: 100)
let w: -Player = weak_of(s)

# Later...
match w.upgrade():
    case Some(strong):
        print "Player still alive: {strong.name}"
    case None:
        print "Player was freed"
```

### Handle Pointer: `+T`

`+T` is a handle pointer:

- A small ID (typically `(slot_index, generation)`) into a global handle pool for type `T`
- Non-owning; lifetime is controlled by the pool, not the handle
- Dereference always goes through the global pool
- Cheap to copy (like an integer)

```simple
let h: +Enemy = new+ Enemy(hp: 100, pos: (0, 0))
# h is a lightweight handle into the global Enemy pool
```

**Important constraints**:

- For each concrete type `T`, there is **at most one** handle pool
- That pool must be defined at **global scope**
- `+T` handles are only valid relative to that single global pool for `T`

---

## Pointer Type Summary

| Type | Ownership | Lifetime Control |
|------|-----------|------------------|
| `T` | GC-managed | Garbage collector |
| `&T` | Unique owner | RAII (freed when owner drops) |
| `*T` | Shared owners | Reference count (freed at zero) |
| `-T` | Non-owning | Controlled by `*T` or GC |
| `+T` | Non-owning | Controlled by global handle pool |

| Type | Freed When |
|------|------------|
| `&T` | Last `&T` binding goes out of scope |
| `*T` | Reference count reaches zero |
| `-T` | Never frees (non-owning) |
| `+T` | Never frees; pool's `handle_free` or compaction |
| `T` (GC) | GC determines unreachability |

---

## Allocation Forms (`new` Variants)

There is no generic `new`. The allocation form explicitly encodes ownership semantics:

| Form | Returns | Ownership |
|------|---------|-----------|
| `new(&) T(...)` | `&T` | Unique (move-only, RAII) |
| `new* T(...)` | `*T` | Shared (refcounted) |
| `new- T(...)` | `-T` | Weak (non-owning) |
| `new+ T(...)` | `+T` | Handle (pool-managed) |

### Unique Allocation: `new(&) T(...) → &T`

```simple
let u: &Player = new(&) Player(name: "Unique", hp: 100)
```

Semantics:

- Allocate `T` on the manual heap
- Return unique pointer `&T`
- `&T` is move-only:
  - `let b = u` → compile error (implicit copy)
  - `let b = move u` → OK; `u` becomes unusable
- When the `&T` binding goes out of scope, destructor runs and memory is freed

### Shared Allocation: `new* T(...) → *T`

```simple
let s: *Player = new* Player(name: "Shared", hp: 100)
```

Semantics:

- Allocate `T` with an embedded reference count
- Return shared pointer `*T`
- Copying `*T` increments the reference count
- When reference count reaches zero, destructor runs and memory is freed

### Weak Allocation: `new- T(...) → -T`

```simple
let w: -Player = new- Player(name: "Ephemeral", hp: 50)
```

Semantics:

- Convenience for creating a weak pointer to a freshly allocated shared object
- Equivalent to:
  ```simple
  let s: *Player = new* Player(name: "Ephemeral", hp: 50)
  let w: -Player = weak_of(s)
  ```
- `w` never owns; dropping `w` does not affect the object's lifetime
- Use `w.upgrade()` to get `*T?` (returns `None` if object was freed)

### Handle Allocation: `new+ T(...) → +T`

```simple
let h: +Enemy = new+ Enemy(hp: 100, pos: (0, 0))
```

Semantics:

- Uses the **single global handle pool** for type `Enemy`
- Allocates a slot in that pool, constructs `Enemy` in that slot
- Returns a handle `+Enemy` pointing to that slot
- `+T` is cheap to copy (it's just an ID)
- Dropping `+T` does **not** free the object; the pool controls lifetime

---

## Global Handle Pools

For each handle-eligible type `T`:

- There can be **at most one** handle pool
- It **must** be declared at global scope

### Declaration Syntax

```simple
handle_pool Enemy:
    capacity: 1024
```

Semantics:

- Declares the global handle pool for `Enemy`
- All uses of `new+ Enemy(...)` and handle operations for `+Enemy` refer to this pool

### Pool Rules

1. **Exactly one pool per type**: Multiple `handle_pool Enemy` declarations produce a compile-time error

2. **Pool required for `new+`**: If code uses `new+ T(...)` without a declared `handle_pool T`:
   ```
   error: No global handle pool for type T
   ```

3. **Global scope only**: Declaring `handle_pool` inside a function, actor, or block produces a compile-time error

### Using Handles at Runtime

```simple
handle_pool Enemy:
    capacity: 1024

let h: +Enemy = new+ Enemy(hp: 100, pos: (0, 0))
```

**Accessing handle data**:

```simple
# Mutable access
match Enemy.handle_get_mut(h):
    case Some(e):
        e.hp -= 10
    case None:
        log "Enemy not found"

# Read-only access
match Enemy.handle_get(h):
    case Some(e):
        print "Enemy HP: {e.hp}"
    case None:
        log "Enemy not found"
```

**Freeing a handle**:

```simple
Enemy.handle_free(h)   # Invalidate handle, recycle slot
```

---

## Borrowing

Borrow types provide non-owning temporary references:

| Borrow Type | Description |
|-------------|-------------|
| `&T_borrow` | Immutable borrow |
| `&mut T_borrow` | Mutable borrow |

Borrows can reference data inside:
- GC-managed `T`
- Unique `&T`
- Shared `*T`
- Handle pool slots

The compiler enforces that **borrows never outlive their source**:

```simple
fn damage_enemy(h: +Enemy, amount: i32):
    match Enemy.handle_get_mut(h):
        case Some(e):      # e is a short-lived mutable borrow
            e.hp -= amount
            # e cannot escape this scope
        case None:
            log "Enemy not found"
```

---

## Compile-Time Checks

### For `+T` / `new+`

1. **Pool requirement**: Use of `new+ T(...)` is only valid if a single global `handle_pool T` exists
   - No pool → compile error
   - More than one pool → compile error

2. **No local pools**: `handle_pool T` is only allowed at top-level (global) scope
   - Inside function, actor, or block → compile error

3. **Type match**: `new+ T(...)` and all `T.handle_*` operations are bound to the pool for exactly that `T`

---

## Choosing the Right Pointer Type

| Use Case | Recommended Type |
|----------|------------------|
| General application code | `T` (GC) |
| Single owner, deterministic cleanup | `&T` (unique) |
| Multiple owners, shared lifetime | `*T` (shared) |
| Observer pattern, caches | `-T` (weak) |
| Entity systems, game objects, pools | `+T` (handle) |

---

## Example: Game Entity System with Handles

```simple
handle_pool Enemy:
    capacity: 10000

handle_pool Projectile:
    capacity: 50000

actor GameWorld:
    state:
        enemies: List[+Enemy] = []
        projectiles: List[+Projectile] = []

    on SpawnEnemy(pos: Vec2, hp: i32) async:
        let h: +Enemy = new+ Enemy(pos: pos, hp: hp)
        self.enemies->push(h)

    on Tick(dt: f64) async:
        # Update projectiles
        for proj_handle in self.projectiles:
            match Projectile.handle_get_mut(proj_handle):
                case Some(proj):
                    proj.pos = proj.pos + proj.vel * dt
                    match Enemy.handle_get_mut(proj.target):
                        case Some(enemy):
                            if distance(proj.pos, enemy.pos) < HIT_RADIUS:
                                enemy.hp -= DAMAGE
                                Projectile.handle_free(proj_handle)
                        case None:
                            Projectile.handle_free(proj_handle)
                case None:
                    pass

        # Compact lists (remove freed handles)
        self.enemies->retain(\h: Enemy.handle_valid(h))
        self.projectiles->retain(\h: Projectile.handle_valid(h))
```

This demonstrates:
- Separate handle pools for different entity types
- Handles stored in collections (cheap to copy)
- Safe access patterns with `handle_get`/`handle_get_mut`
- Explicit lifetime control via `handle_free`
- Validation with `handle_valid`

---

## Note on Option Types

Handle operations like `handle_get`, `handle_get_mut`, and `weak.upgrade()` return `Option[T]` to enforce explicit handling of missing values:

```simple
# Option enforces safe access patterns
match Enemy.handle_get_mut(h):
    case Some(enemy):
        enemy.hp -= 10
    case None:
        log "Enemy not found"
```

Simple requires explicit `Option[T]` - implicit `nil` returns are compile errors. See [Unit Types](units.md) for the complete type safety policy.

---

## Related Specifications

- [Types and Mutability](types.md)
- [Unit Types](units.md)
- [Data Structures](data_structures.md)
- [Concurrency](concurrency.md)
