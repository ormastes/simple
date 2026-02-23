# Simple Language Memory and Ownership - Test Specification

> **⚠️ GENERATED FILE** - Do not edit directly!
> **Source:** `tests/specs/memory_spec.spl`
> **Generated:** 2026-01-10 04:47:40
>
> To update this file, edit the source _spec.spl file and run:
> ```bash
> python scripts/spec_gen.py --input tests/specs/memory_spec.spl
> ```

**Status:** Reference
**Feature IDs:** **Source:** memory.md
**Note:** This is a test extraction file. For complete specification text,

## Quick Navigation

- [Overview](#overview)
- [Symbols Reference](#symbols-reference)
- [Test Cases](#test-cases) (17 tests)
- [Source Code](#source-code)

## Overview

This file contains executable test cases extracted from memory.md.
The original specification file remains as architectural reference documentation.

**Note:** This is a test extraction file. For complete specification text,
design rationale, and architecture, see doc/spec/memory.md

---

## Symbols Reference

| Symbol | Used in Tests |
|--------|---------------|
| `Allocation` | [6](#allocation_forms_new_variants_6), [7](#allocation_forms_new_variants_7), [8](#allocation_forms_new_variants_8), [9](#allocation_forms_new_variants_9), [10](#allocation_forms_new_variants_10) |
| `AllocationFormsNewVariants` | [6](#allocation_forms_new_variants_6), [7](#allocation_forms_new_variants_7), [8](#allocation_forms_new_variants_8), [9](#allocation_forms_new_variants_9), [10](#allocation_forms_new_variants_10) |
| `And` | [1](#reference_and_pointer_kinds_1), [2](#reference_and_pointer_kinds_2), [3](#reference_and_pointer_kinds_3), [4](#reference_and_pointer_kinds_4), [5](#reference_and_pointer_kinds_5) |
| `Compact` | [16](#example_game_entity_system_with_handles_16) |
| `DAMAGE` | [16](#example_game_entity_system_with_handles_16) |
| `Damage` | [15](#damage_enemy) |
| `DamageEnemy` | [15](#damage_enemy) |
| `Enemy` | [5](#reference_and_pointer_kinds_5), [10](#allocation_forms_new_variants_10), [11](#global_handle_pools_11), [12](#global_handle_pools_12), [13](#global_handle_pools_13), ... (9 total) |
| `Entity` | [16](#example_game_entity_system_with_handles_16) |
| `Ephemeral` | [8](#allocation_forms_new_variants_8), [9](#allocation_forms_new_variants_9) |
| `Example` | [16](#example_game_entity_system_with_handles_16) |
| `ExampleGameEntitySystemWithHandles` | [16](#example_game_entity_system_with_handles_16) |
| `Forms` | [6](#allocation_forms_new_variants_6), [7](#allocation_forms_new_variants_7), [8](#allocation_forms_new_variants_8), [9](#allocation_forms_new_variants_9), [10](#allocation_forms_new_variants_10) |
| `Game` | [16](#example_game_entity_system_with_handles_16) |
| `GameWorld` | [16](#example_game_entity_system_with_handles_16) |
| `Global` | [11](#global_handle_pools_11), [12](#global_handle_pools_12), [13](#global_handle_pools_13), [14](#global_handle_pools_14) |
| `GlobalHandlePools` | [11](#global_handle_pools_11), [12](#global_handle_pools_12), [13](#global_handle_pools_13), [14](#global_handle_pools_14) |
| `Handle` | [11](#global_handle_pools_11), [12](#global_handle_pools_12), [13](#global_handle_pools_13), [14](#global_handle_pools_14) |
| `Handles` | [16](#example_game_entity_system_with_handles_16) |
| `Hero` | [1](#reference_and_pointer_kinds_1) |
| `Invalidate` | [14](#global_handle_pools_14) |
| `Kinds` | [1](#reference_and_pointer_kinds_1), [2](#reference_and_pointer_kinds_2), [3](#reference_and_pointer_kinds_3), [4](#reference_and_pointer_kinds_4), [5](#reference_and_pointer_kinds_5) |
| `Later` | [4](#reference_and_pointer_kinds_4) |
| `List` | [16](#example_game_entity_system_with_handles_16) |
| `Mutable` | [13](#global_handle_pools_13) |
| `New` | [6](#allocation_forms_new_variants_6), [7](#allocation_forms_new_variants_7), [8](#allocation_forms_new_variants_8), [9](#allocation_forms_new_variants_9), [10](#allocation_forms_new_variants_10) |
| `Note` | [17](#note_on_option_types_17) |
| `NoteOnOptionTypes` | [17](#note_on_option_types_17) |
| `Object` | [3](#reference_and_pointer_kinds_3) |
| `Option` | [17](#note_on_option_types_17) |
| `Player` | [1](#reference_and_pointer_kinds_1), [2](#reference_and_pointer_kinds_2), [3](#reference_and_pointer_kinds_3), [4](#reference_and_pointer_kinds_4), [6](#allocation_forms_new_variants_6), ... (8 total) |
| `Pointer` | [1](#reference_and_pointer_kinds_1), [2](#reference_and_pointer_kinds_2), [3](#reference_and_pointer_kinds_3), [4](#reference_and_pointer_kinds_4), [5](#reference_and_pointer_kinds_5) |
| `Pools` | [11](#global_handle_pools_11), [12](#global_handle_pools_12), [13](#global_handle_pools_13), [14](#global_handle_pools_14) |
| `Projectile` | [16](#example_game_entity_system_with_handles_16) |
| `Read` | [13](#global_handle_pools_13) |
| `Reference` | [1](#reference_and_pointer_kinds_1), [2](#reference_and_pointer_kinds_2), [3](#reference_and_pointer_kinds_3), [4](#reference_and_pointer_kinds_4), [5](#reference_and_pointer_kinds_5) |
| `ReferenceAndPointerKinds` | [1](#reference_and_pointer_kinds_1), [2](#reference_and_pointer_kinds_2), [3](#reference_and_pointer_kinds_3), [4](#reference_and_pointer_kinds_4), [5](#reference_and_pointer_kinds_5) |
| `Shared` | [3](#reference_and_pointer_kinds_3), [7](#allocation_forms_new_variants_7) |
| `Solo` | [2](#reference_and_pointer_kinds_2) |
| `SpawnEnemy` | [16](#example_game_entity_system_with_handles_16) |
| `System` | [16](#example_game_entity_system_with_handles_16) |
| `Target` | [4](#reference_and_pointer_kinds_4) |
| `Tick` | [16](#example_game_entity_system_with_handles_16) |
| `Types` | [17](#note_on_option_types_17) |
| `Unique` | [6](#allocation_forms_new_variants_6) |
| `Update` | [16](#example_game_entity_system_with_handles_16) |
| `Variants` | [6](#allocation_forms_new_variants_6), [7](#allocation_forms_new_variants_7), [8](#allocation_forms_new_variants_8), [9](#allocation_forms_new_variants_9), [10](#allocation_forms_new_variants_10) |
| `Vec2` | [16](#example_game_entity_system_with_handles_16) |
| `With` | [16](#example_game_entity_system_with_handles_16) |
| `allocation` | [6](#allocation_forms_new_variants_6), [7](#allocation_forms_new_variants_7), [8](#allocation_forms_new_variants_8), [9](#allocation_forms_new_variants_9), [10](#allocation_forms_new_variants_10) |
| `allocation_forms_new_variants` | [6](#allocation_forms_new_variants_6), [7](#allocation_forms_new_variants_7), [8](#allocation_forms_new_variants_8), [9](#allocation_forms_new_variants_9), [10](#allocation_forms_new_variants_10) |
| `and` | [1](#reference_and_pointer_kinds_1), [2](#reference_and_pointer_kinds_2), [3](#reference_and_pointer_kinds_3), [4](#reference_and_pointer_kinds_4), [5](#reference_and_pointer_kinds_5) |
| `assert_compiles` | [1](#reference_and_pointer_kinds_1), [2](#reference_and_pointer_kinds_2), [3](#reference_and_pointer_kinds_3), [4](#reference_and_pointer_kinds_4), [5](#reference_and_pointer_kinds_5), ... (16 total) |
| `damage` | [15](#damage_enemy) |
| `damage_enemy` | [15](#damage_enemy) |
| `distance` | [16](#example_game_entity_system_with_handles_16) |
| `enemy` | [15](#damage_enemy) |
| `entity` | [16](#example_game_entity_system_with_handles_16) |
| `example` | [16](#example_game_entity_system_with_handles_16) |
| `example_game_entity_system_with_handles` | [16](#example_game_entity_system_with_handles_16) |
| `forms` | [6](#allocation_forms_new_variants_6), [7](#allocation_forms_new_variants_7), [8](#allocation_forms_new_variants_8), [9](#allocation_forms_new_variants_9), [10](#allocation_forms_new_variants_10) |
| `game` | [16](#example_game_entity_system_with_handles_16) |
| `global` | [11](#global_handle_pools_11), [12](#global_handle_pools_12), [13](#global_handle_pools_13), [14](#global_handle_pools_14) |
| `global_handle_pools` | [11](#global_handle_pools_11), [12](#global_handle_pools_12), [13](#global_handle_pools_13), [14](#global_handle_pools_14) |
| `handle` | [11](#global_handle_pools_11), [12](#global_handle_pools_12), [13](#global_handle_pools_13), [14](#global_handle_pools_14) |
| `handle_free` | [14](#global_handle_pools_14), [16](#example_game_entity_system_with_handles_16) |
| `handle_get` | [13](#global_handle_pools_13) |
| `handle_get_mut` | [13](#global_handle_pools_13), [15](#damage_enemy), [16](#example_game_entity_system_with_handles_16), [17](#note_on_option_types_17) |
| `handle_valid` | [16](#example_game_entity_system_with_handles_16) |
| `handles` | [16](#example_game_entity_system_with_handles_16) |
| `kinds` | [1](#reference_and_pointer_kinds_1), [2](#reference_and_pointer_kinds_2), [3](#reference_and_pointer_kinds_3), [4](#reference_and_pointer_kinds_4), [5](#reference_and_pointer_kinds_5) |
| `lists` | [16](#example_game_entity_system_with_handles_16) |
| `new` | [2](#reference_and_pointer_kinds_2), [6](#allocation_forms_new_variants_6), [7](#allocation_forms_new_variants_7), [8](#allocation_forms_new_variants_8), [9](#allocation_forms_new_variants_9), ... (6 total) |
| `note` | [17](#note_on_option_types_17) |
| `note_on_option_types` | [17](#note_on_option_types_17) |
| `option` | [17](#note_on_option_types_17) |
| `pointer` | [1](#reference_and_pointer_kinds_1), [2](#reference_and_pointer_kinds_2), [3](#reference_and_pointer_kinds_3), [4](#reference_and_pointer_kinds_4), [5](#reference_and_pointer_kinds_5) |
| `pools` | [11](#global_handle_pools_11), [12](#global_handle_pools_12), [13](#global_handle_pools_13), [14](#global_handle_pools_14) |
| `push` | [16](#example_game_entity_system_with_handles_16) |
| `reference` | [1](#reference_and_pointer_kinds_1), [2](#reference_and_pointer_kinds_2), [3](#reference_and_pointer_kinds_3), [4](#reference_and_pointer_kinds_4), [5](#reference_and_pointer_kinds_5) |
| `reference_and_pointer_kinds` | [1](#reference_and_pointer_kinds_1), [2](#reference_and_pointer_kinds_2), [3](#reference_and_pointer_kinds_3), [4](#reference_and_pointer_kinds_4), [5](#reference_and_pointer_kinds_5) |
| `retain` | [16](#example_game_entity_system_with_handles_16) |
| `system` | [16](#example_game_entity_system_with_handles_16) |
| `types` | [17](#note_on_option_types_17) |
| `unusable` | [2](#reference_and_pointer_kinds_2) |
| `upgrade` | [4](#reference_and_pointer_kinds_4) |
| `variants` | [6](#allocation_forms_new_variants_6), [7](#allocation_forms_new_variants_7), [8](#allocation_forms_new_variants_8), [9](#allocation_forms_new_variants_9), [10](#allocation_forms_new_variants_10) |
| `weak_of` | [4](#reference_and_pointer_kinds_4), [9](#allocation_forms_new_variants_9) |
| `with` | [16](#example_game_entity_system_with_handles_16) |

---

## Test Cases (17 total)

| # | Test | Section | Symbols |
|---|------|---------|---------|
| 1 | [reference_and_pointer_kinds_1](#reference_and_pointer_kinds_1) | Reference and Pointer Kinds | `and`, `reference`, `Reference` +10 |
| 2 | [reference_and_pointer_kinds_2](#reference_and_pointer_kinds_2) | Reference and Pointer Kinds | `and`, `reference`, `Reference` +12 |
| 3 | [reference_and_pointer_kinds_3](#reference_and_pointer_kinds_3) | Reference and Pointer Kinds | `and`, `reference`, `Reference` +11 |
| 4 | [reference_and_pointer_kinds_4](#reference_and_pointer_kinds_4) | Reference and Pointer Kinds | `and`, `reference`, `Reference` +13 |
| 5 | [reference_and_pointer_kinds_5](#reference_and_pointer_kinds_5) | Reference and Pointer Kinds | `and`, `reference`, `Reference` +9 |
| 6 | [allocation_forms_new_variants_6](#allocation_forms_new_variants_6) | Allocation Forms (`new` Variants) | `new`, `variants`, `Variants` +10 |
| 7 | [allocation_forms_new_variants_7](#allocation_forms_new_variants_7) | Allocation Forms (`new` Variants) | `new`, `variants`, `Variants` +10 |
| 8 | [allocation_forms_new_variants_8](#allocation_forms_new_variants_8) | Allocation Forms (`new` Variants) | `new`, `variants`, `Variants` +10 |
| 9 | [allocation_forms_new_variants_9](#allocation_forms_new_variants_9) | Allocation Forms (`new` Variants) | `new`, `variants`, `Variants` +11 |
| 10 | [allocation_forms_new_variants_10](#allocation_forms_new_variants_10) | Allocation Forms (`new` Variants) | `new`, `variants`, `Variants` +9 |
| 11 | [global_handle_pools_11](#global_handle_pools_11) | Global Handle Pools | `Global`, `GlobalHandlePools`, `Handle` +7 |
| 12 | [global_handle_pools_12](#global_handle_pools_12) | Global Handle Pools | `Global`, `GlobalHandlePools`, `Handle` +7 |
| 13 | [global_handle_pools_13](#global_handle_pools_13) | Global Handle Pools | `Global`, `GlobalHandlePools`, `Handle` +11 |
| 14 | [global_handle_pools_14](#global_handle_pools_14) | Global Handle Pools | `Global`, `GlobalHandlePools`, `Handle` +9 |
| 15 | [damage_enemy](#damage_enemy) | Borrowing | `DamageEnemy`, `damage_enemy`, `Damage` +4 |
| 16 | [example_game_entity_system_with_handles_16](#example_game_entity_system_with_handles_16) | Example: Game Entity System with Handles | `Game`, `system`, `ExampleGameEntitySystemWithHandles` +29 |
| 17 | [note_on_option_types_17](#note_on_option_types_17) | Note on Option Types | `types`, `Types`, `Option` +8 |

---

### Test 1: Reference and Pointer Kinds {#reference_and_pointer_kinds_1}

*Source line: ~7*

**Test name:** `reference_and_pointer_kinds_1`

**Description:**

A bare type `T` is a GC-managed reference to a heap object:

**Linked Symbols:**
- `and`
- `reference`
- `Reference`
- `Pointer`
- `kinds`
- `pointer`
- `Kinds`
- `ReferenceAndPointerKinds`
- `reference_and_pointer_kinds`
- `And`
- ... and 3 more

**Code:**

```simple
test "reference_and_pointer_kinds_1":
    let p: Player = Player(name: "Hero", hp: 100)
    assert_compiles()
```

### Test 2: Reference and Pointer Kinds {#reference_and_pointer_kinds_2}

*Source line: ~21*

**Test name:** `reference_and_pointer_kinds_2`

**Description:**

- Exactly one owner at a time
- Move-only (cannot be copied)
- When the `&T` goes out of scope, the ...

**Linked Symbols:**
- `and`
- `reference`
- `Reference`
- `Pointer`
- `kinds`
- `pointer`
- `Kinds`
- `ReferenceAndPointerKinds`
- `reference_and_pointer_kinds`
- `And`
- ... and 5 more

**Code:**

```simple
test "reference_and_pointer_kinds_2":
    let u: &Player = new(&) Player(name: "Solo", hp: 50)
    # u is the sole owner

    let v = move u    # ownership transferred to v
    # u is now unusable (compile error if accessed)
    assert_compiles()
```

### Test 3: Reference and Pointer Kinds {#reference_and_pointer_kinds_3}

*Source line: ~37*

**Test name:** `reference_and_pointer_kinds_3`

**Description:**

- Multiple owners allowed
- Copying/cloning increments the reference count
- Object freed when refer...

**Linked Symbols:**
- `and`
- `reference`
- `Reference`
- `Pointer`
- `kinds`
- `pointer`
- `Kinds`
- `ReferenceAndPointerKinds`
- `reference_and_pointer_kinds`
- `And`
- ... and 4 more

**Code:**

```simple
test "reference_and_pointer_kinds_3":
    let s1: *Player = new* Player(name: "Shared", hp: 75)
    let s2 = s1       # refcount incremented, both own the object
    # Object freed when both s1 and s2 go out of scope
    assert_compiles()
```

### Test 4: Reference and Pointer Kinds {#reference_and_pointer_kinds_4}

*Source line: ~51*

**Test name:** `reference_and_pointer_kinds_4`

**Description:**

- Non-owning reference to an object managed by `*T` (or GC)
- Does not keep the object alive
- Must ...

**Linked Symbols:**
- `and`
- `reference`
- `Reference`
- `Pointer`
- `kinds`
- `pointer`
- `Kinds`
- `ReferenceAndPointerKinds`
- `reference_and_pointer_kinds`
- `And`
- ... and 6 more

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

### Test 5: Reference and Pointer Kinds {#reference_and_pointer_kinds_5}

*Source line: ~72*

**Test name:** `reference_and_pointer_kinds_5`

**Description:**

- A small ID (typically `(slot_index, generation)`) into a global handle pool for type `T`
- Non-own...

**Linked Symbols:**
- `and`
- `reference`
- `Reference`
- `Pointer`
- `kinds`
- `pointer`
- `Kinds`
- `ReferenceAndPointerKinds`
- `reference_and_pointer_kinds`
- `And`
- ... and 2 more

**Code:**

```simple
test "reference_and_pointer_kinds_5":
    let h: +Enemy = new+ Enemy(hp: 100, pos: (0, 0))
    # h is a lightweight handle into the global Enemy pool
    assert_compiles()
```

### Test 6: Allocation Forms (`new` Variants) {#allocation_forms_new_variants_6}

*Source line: ~14*

**Test name:** `allocation_forms_new_variants_6`

**Description:**

| Form | Returns | Ownership |
|------|---------|-----------|
| `new(&) T(...)` | `&T` | Unique (mov...

**Linked Symbols:**
- `new`
- `variants`
- `Variants`
- `allocation_forms_new_variants`
- `forms`
- `allocation`
- `Allocation`
- `New`
- `AllocationFormsNewVariants`
- `Forms`
- ... and 3 more

**Code:**

```simple
test "allocation_forms_new_variants_6":
    let u: &Player = new(&) Player(name: "Unique", hp: 100)
    assert_compiles()
```

### Test 7: Allocation Forms (`new` Variants) {#allocation_forms_new_variants_7}

*Source line: ~29*

**Test name:** `allocation_forms_new_variants_7`

**Description:**

- Allocate `T` on the manual heap
- Return unique pointer `&T`
- `&T` is move-only:
  - `let b = u` ...

**Linked Symbols:**
- `new`
- `variants`
- `Variants`
- `allocation_forms_new_variants`
- `forms`
- `allocation`
- `Allocation`
- `New`
- `AllocationFormsNewVariants`
- `Forms`
- ... and 3 more

**Code:**

```simple
test "allocation_forms_new_variants_7":
    let s: *Player = new* Player(name: "Shared", hp: 100)
    assert_compiles()
```

### Test 8: Allocation Forms (`new` Variants) {#allocation_forms_new_variants_8}

*Source line: ~42*

**Test name:** `allocation_forms_new_variants_8`

**Description:**

- Allocate `T` with an embedded reference count
- Return shared pointer `*T`
- Copying `*T` incremen...

**Linked Symbols:**
- `new`
- `variants`
- `Variants`
- `allocation_forms_new_variants`
- `forms`
- `allocation`
- `Allocation`
- `New`
- `AllocationFormsNewVariants`
- `Forms`
- ... and 3 more

**Code:**

```simple
test "allocation_forms_new_variants_8":
    let w: -Player = new- Player(name: "Ephemeral", hp: 50)
    assert_compiles()
```

### Test 9: Allocation Forms (`new` Variants) {#allocation_forms_new_variants_9}

*Source line: ~50*

**Test name:** `allocation_forms_new_variants_9`

**Description:**

- Convenience for creating a weak pointer to a freshly allocated shared object
- Equivalent to:

**Linked Symbols:**
- `new`
- `variants`
- `Variants`
- `allocation_forms_new_variants`
- `forms`
- `allocation`
- `Allocation`
- `New`
- `AllocationFormsNewVariants`
- `Forms`
- ... and 4 more

**Code:**

```simple
test "allocation_forms_new_variants_9":
    let s: *Player = new* Player(name: "Ephemeral", hp: 50)
      let w: -Player = weak_of(s)
    assert_compiles()
```

### Test 10: Allocation Forms (`new` Variants) {#allocation_forms_new_variants_10}

*Source line: ~59*

**Test name:** `allocation_forms_new_variants_10`

**Description:**

- Convenience for creating a weak pointer to a freshly allocated shared object
- Equivalent to:
  ``...

**Linked Symbols:**
- `new`
- `variants`
- `Variants`
- `allocation_forms_new_variants`
- `forms`
- `allocation`
- `Allocation`
- `New`
- `AllocationFormsNewVariants`
- `Forms`
- ... and 2 more

**Code:**

```simple
test "allocation_forms_new_variants_10":
    let h: +Enemy = new+ Enemy(hp: 100, pos: (0, 0))
    assert_compiles()
```

### Test 11: Global Handle Pools {#global_handle_pools_11}

*Source line: ~10*

**Test name:** `global_handle_pools_11`

**Description:**

- There can be at most one handle pool
- It must be declared at global scope

**Linked Symbols:**
- `Global`
- `GlobalHandlePools`
- `Handle`
- `Pools`
- `global`
- `pools`
- `handle`
- `global_handle_pools`
- `assert_compiles`
- `Enemy`

**Code:**

```simple
test "global_handle_pools_11":
    handle_pool Enemy:
        capacity: 1024
    assert_compiles()
```

### Test 12: Global Handle Pools {#global_handle_pools_12}

*Source line: ~33*

**Test name:** `global_handle_pools_12`

**Description:**

3. Global scope only: Declaring `handle_pool` inside a function, actor, or block produces a compile-...

**Linked Symbols:**
- `Global`
- `GlobalHandlePools`
- `Handle`
- `Pools`
- `global`
- `pools`
- `handle`
- `global_handle_pools`
- `assert_compiles`
- `Enemy`

**Code:**

```simple
test "global_handle_pools_12":
    handle_pool Enemy:
        capacity: 1024

    let h: +Enemy = new+ Enemy(hp: 100, pos: (0, 0))
    assert_compiles()
```

### Test 13: Global Handle Pools {#global_handle_pools_13}

*Source line: ~42*

**Test name:** `global_handle_pools_13`

**Description:**

Accessing handle data:

**Linked Symbols:**
- `Global`
- `GlobalHandlePools`
- `Handle`
- `Pools`
- `global`
- `pools`
- `handle`
- `global_handle_pools`
- `handle_get_mut`
- `Read`
- ... and 4 more

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

### Test 14: Global Handle Pools {#global_handle_pools_14}

*Source line: ~60*

**Test name:** `global_handle_pools_14`

**Linked Symbols:**
- `Global`
- `GlobalHandlePools`
- `Handle`
- `Pools`
- `global`
- `pools`
- `handle`
- `global_handle_pools`
- `assert_compiles`
- `Enemy`
- ... and 2 more

**Code:**

```simple
test "global_handle_pools_14":
    Enemy.handle_free(h)   # Invalidate handle, recycle slot
    assert_compiles()
```

### Test 15: Borrowing {#damage_enemy}

*Source line: ~18*

**Test name:** `damage_enemy`

**Description:**

The compiler enforces that borrows never outlive their source:

**Linked Symbols:**
- `DamageEnemy`
- `damage_enemy`
- `Damage`
- `damage`
- `enemy`
- `Enemy`
- `handle_get_mut`

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

### Test 16: Example: Game Entity System with Handles {#example_game_entity_system_with_handles_16}

*Source line: ~3*

**Test name:** `example_game_entity_system_with_handles_16`

**Description:**

Example: Game Entity System with Handles

**Linked Symbols:**
- `Game`
- `system`
- `ExampleGameEntitySystemWithHandles`
- `game`
- `example_game_entity_system_with_handles`
- `entity`
- `System`
- `with`
- `handles`
- `example`
- ... and 22 more

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

### Test 17: Note on Option Types {#note_on_option_types_17}

*Source line: ~5*

**Test name:** `note_on_option_types_17`

**Description:**

Handle operations like `handle_get`, `handle_get_mut`, and `weak.upgrade()` return `Option[T]` to en...

**Linked Symbols:**
- `types`
- `Types`
- `Option`
- `NoteOnOptionTypes`
- `note_on_option_types`
- `Note`
- `option`
- `note`
- `assert_compiles`
- `Enemy`
- ... and 1 more

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

## Source Code

**View full specification:** [memory_spec.spl](../../tests/specs/memory_spec.spl)

---

*This file was auto-generated from the executable specification.*
*Source: `tests/specs/memory_spec.spl`*
