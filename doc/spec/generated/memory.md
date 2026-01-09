# Simple Language Memory and Ownership - Test Specification

> **⚠️ GENERATED FILE** - Do not edit directly!
> **Source:** `tests/specs/memory_spec.spl`
> **Generated:** 2026-01-09 04:37:07
>
> To update this file, edit the source _spec.spl file and run:
> ```bash
> python scripts/spec_gen.py --input tests/specs/memory_spec.spl
> ```

**Status:** Reference
**Feature IDs:** **Source:** memory.md
**Note:** This is a test extraction file. For complete specification text,

## Overview

This file contains executable test cases extracted from memory.md.
The original specification file remains as architectural reference documentation.

**Note:** This is a test extraction file. For complete specification text,
design rationale, and architecture, see doc/spec/memory.md

---

## Test Cases (17 total)

| Test | Section | Description |
|------|---------|-------------|
| [reference_and_pointer_kinds_1](#test-1) | Reference and Pointer Kinds | A bare type `T` is a GC-managed reference to a heap object: |
| [reference_and_pointer_kinds_2](#test-2) | Reference and Pointer Kinds | - Exactly one owner at a time... |
| [reference_and_pointer_kinds_3](#test-3) | Reference and Pointer Kinds | - Multiple owners allowed... |
| [reference_and_pointer_kinds_4](#test-4) | Reference and Pointer Kinds | - Non-owning reference to an object managed by `*T` (or GC)... |
| [reference_and_pointer_kinds_5](#test-5) | Reference and Pointer Kinds | - A small ID (typically `(slot_index, generation)`) into a g... |
| [allocation_forms_new_variants_6](#test-6) | Allocation Forms (`new` Variants) | \| Form \| Returns \| Ownership \|... |
| [allocation_forms_new_variants_7](#test-7) | Allocation Forms (`new` Variants) | - Allocate `T` on the manual heap... |
| [allocation_forms_new_variants_8](#test-8) | Allocation Forms (`new` Variants) | - Allocate `T` with an embedded reference count... |
| [allocation_forms_new_variants_9](#test-9) | Allocation Forms (`new` Variants) | - Convenience for creating a weak pointer to a freshly alloc... |
| [allocation_forms_new_variants_10](#test-10) | Allocation Forms (`new` Variants) | - Convenience for creating a weak pointer to a freshly alloc... |
| [global_handle_pools_11](#test-11) | Global Handle Pools | - There can be at most one handle pool... |
| [global_handle_pools_12](#test-12) | Global Handle Pools | 3. Global scope only: Declaring `handle_pool` inside a funct... |
| [global_handle_pools_13](#test-13) | Global Handle Pools | Accessing handle data: |
| [global_handle_pools_14](#test-14) | Global Handle Pools |  |
| [damage_enemy](#test-15) | Borrowing | The compiler enforces that borrows never outlive their sourc... |
| [example_game_entity_system_with_handles_16](#test-16) | Example: Game Entity System with Handles | Example: Game Entity System with Handles |
| [note_on_option_types_17](#test-17) | Note on Option Types | Handle operations like `handle_get`, `handle_get_mut`, and `... |

---

### Test 1: Reference and Pointer Kinds

*Source line: ~7*

**Test name:** `reference_and_pointer_kinds_1`

**Description:**

A bare type `T` is a GC-managed reference to a heap object:

**Code:**

```simple
test "reference_and_pointer_kinds_1":
    let p: Player = Player(name: "Hero", hp: 100)
    assert_compiles()
```

### Test 2: Reference and Pointer Kinds

*Source line: ~21*

**Test name:** `reference_and_pointer_kinds_2`

**Description:**

- Exactly one owner at a time
- Move-only (cannot be copied)
- When the `&T` goes out of scope, the ...

**Code:**

```simple
test "reference_and_pointer_kinds_2":
    let u: &Player = new(&) Player(name: "Solo", hp: 50)
    # u is the sole owner

    let v = move u    # ownership transferred to v
    # u is now unusable (compile error if accessed)
    assert_compiles()
```

### Test 3: Reference and Pointer Kinds

*Source line: ~37*

**Test name:** `reference_and_pointer_kinds_3`

**Description:**

- Multiple owners allowed
- Copying/cloning increments the reference count
- Object freed when refer...

**Code:**

```simple
test "reference_and_pointer_kinds_3":
    let s1: *Player = new* Player(name: "Shared", hp: 75)
    let s2 = s1       # refcount incremented, both own the object
    # Object freed when both s1 and s2 go out of scope
    assert_compiles()
```

### Test 4: Reference and Pointer Kinds

*Source line: ~51*

**Test name:** `reference_and_pointer_kinds_4`

**Description:**

- Non-owning reference to an object managed by `*T` (or GC)
- Does not keep the object alive
- Must ...

**Code:**

```simple
test "reference_and_pointer_kinds_4":
    let s: *Player = new* Player(name: "Target", hp: 100)
    let w: -Player = weak_of(s)

    # Later...
    match w.upgrade():
        case Some(strong):
            print "Player still alive: {strong.name}"
        case None:
            print "Player was freed"
    assert_compiles()
```

### Test 5: Reference and Pointer Kinds

*Source line: ~72*

**Test name:** `reference_and_pointer_kinds_5`

**Description:**

- A small ID (typically `(slot_index, generation)`) into a global handle pool for type `T`
- Non-own...

**Code:**

```simple
test "reference_and_pointer_kinds_5":
    let h: +Enemy = new+ Enemy(hp: 100, pos: (0, 0))
    # h is a lightweight handle into the global Enemy pool
    assert_compiles()
```

### Test 6: Allocation Forms (`new` Variants)

*Source line: ~14*

**Test name:** `allocation_forms_new_variants_6`

**Description:**

| Form | Returns | Ownership |
|------|---------|-----------|
| `new(&) T(...)` | `&T` | Unique (mov...

**Code:**

```simple
test "allocation_forms_new_variants_6":
    let u: &Player = new(&) Player(name: "Unique", hp: 100)
    assert_compiles()
```

### Test 7: Allocation Forms (`new` Variants)

*Source line: ~29*

**Test name:** `allocation_forms_new_variants_7`

**Description:**

- Allocate `T` on the manual heap
- Return unique pointer `&T`
- `&T` is move-only:
  - `let b = u` ...

**Code:**

```simple
test "allocation_forms_new_variants_7":
    let s: *Player = new* Player(name: "Shared", hp: 100)
    assert_compiles()
```

### Test 8: Allocation Forms (`new` Variants)

*Source line: ~42*

**Test name:** `allocation_forms_new_variants_8`

**Description:**

- Allocate `T` with an embedded reference count
- Return shared pointer `*T`
- Copying `*T` incremen...

**Code:**

```simple
test "allocation_forms_new_variants_8":
    let w: -Player = new- Player(name: "Ephemeral", hp: 50)
    assert_compiles()
```

### Test 9: Allocation Forms (`new` Variants)

*Source line: ~50*

**Test name:** `allocation_forms_new_variants_9`

**Description:**

- Convenience for creating a weak pointer to a freshly allocated shared object
- Equivalent to:

**Code:**

```simple
test "allocation_forms_new_variants_9":
    let s: *Player = new* Player(name: "Ephemeral", hp: 50)
      let w: -Player = weak_of(s)
    assert_compiles()
```

### Test 10: Allocation Forms (`new` Variants)

*Source line: ~59*

**Test name:** `allocation_forms_new_variants_10`

**Description:**

- Convenience for creating a weak pointer to a freshly allocated shared object
- Equivalent to:
  ``...

**Code:**

```simple
test "allocation_forms_new_variants_10":
    let h: +Enemy = new+ Enemy(hp: 100, pos: (0, 0))
    assert_compiles()
```

### Test 11: Global Handle Pools

*Source line: ~10*

**Test name:** `global_handle_pools_11`

**Description:**

- There can be at most one handle pool
- It must be declared at global scope

**Code:**

```simple
test "global_handle_pools_11":
    handle_pool Enemy:
        capacity: 1024
    assert_compiles()
```

### Test 12: Global Handle Pools

*Source line: ~33*

**Test name:** `global_handle_pools_12`

**Description:**

3. Global scope only: Declaring `handle_pool` inside a function, actor, or block produces a compile-...

**Code:**

```simple
test "global_handle_pools_12":
    handle_pool Enemy:
        capacity: 1024

    let h: +Enemy = new+ Enemy(hp: 100, pos: (0, 0))
    assert_compiles()
```

### Test 13: Global Handle Pools

*Source line: ~42*

**Test name:** `global_handle_pools_13`

**Description:**

Accessing handle data:

**Code:**

```simple
test "global_handle_pools_13":
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
    assert_compiles()
```

### Test 14: Global Handle Pools

*Source line: ~60*

**Test name:** `global_handle_pools_14`

**Code:**

```simple
test "global_handle_pools_14":
    Enemy.handle_free(h)   # Invalidate handle, recycle slot
    assert_compiles()
```

### Test 15: Borrowing

*Source line: ~18*

**Test name:** `damage_enemy`

**Description:**

The compiler enforces that borrows never outlive their source:

**Code:**

```simple
fn damage_enemy(h: +Enemy, amount: i32):
    match Enemy.handle_get_mut(h):
        case Some(e):      # e is a short-lived mutable borrow
            e.hp -= amount
            # e cannot escape this scope
        case None:
            log "Enemy not found"
```

### Test 16: Example: Game Entity System with Handles

*Source line: ~3*

**Test name:** `example_game_entity_system_with_handles_16`

**Description:**

Example: Game Entity System with Handles

**Code:**

```simple
test "example_game_entity_system_with_handles_16":
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
    assert_compiles()
```

### Test 17: Note on Option Types

*Source line: ~5*

**Test name:** `note_on_option_types_17`

**Description:**

Handle operations like `handle_get`, `handle_get_mut`, and `weak.upgrade()` return `Option[T]` to en...

**Code:**

```simple
test "note_on_option_types_17":
    # Option enforces safe access patterns
    match Enemy.handle_get_mut(h):
        case Some(enemy):
            enemy.hp -= 10
        case None:
            log "Enemy not found"
    assert_compiles()
```

---

*This file was auto-generated from the executable specification.*
*Source: `tests/specs/memory_spec.spl`*
