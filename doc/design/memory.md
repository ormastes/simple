# Memory Design: GC + Manual Cooperation

> **Version:** 2.0
> **Last Updated:** 2026-01-19
> **Related:** `doc/plan/manual_memory_safety_plan.md`

## Overview

Simple uses a two-domain memory model:
1. **GC Domain** (default) - Automatic memory management
2. **Manual Domain** (opt-in) - Explicit ownership control

---

## Pointer Types

| Syntax | Name | Domain | Ownership | Mutation | Thread-Safe |
|--------|------|--------|-----------|----------|-------------|
| `T` | GC Reference | GC | GC-managed | Via `mut` | N/A |
| `&T` | Unique | Manual | Single owner | Via `mut` | N/A |
| `*T` | Shared (Rc) | Manual | Ref-counted | Read-only (COW) | No |
| `@T` | Atomic (Arc) | Manual | Atomic ref-counted | Read-only (COW) | **Yes** |
| `-T` | Weak | Manual | Non-owning | N/A | Depends |
| `+T` | Handle | Manual | Pool-managed | Via pool | N/A |

**Note:** `T` resolves to:
- **GC mode (default):** GC-managed reference
- **No-GC mode:** `&T` (unique borrowed reference)

**Reference Capabilities:**

| Keyword | Symbol | Name | Aliasing | Transferable |
|---------|--------|------|----------|--------------|
| (none) | `T` | Shared (Imm) | Multiple readers | Copy |
| `mut` | `mut T` | Exclusive (Mut) | Single writer | No |
| `iso` | `~T` | Isolated (Iso) | No aliasing | **Move** |

Capabilities can combine with pointer types:
- `~@Data` - Isolated atomic pointer (thread-safe + transferable)
- `mut *Data` - Mutable shared pointer (single writer to Rc)

---

## GC Domain (Default)

```simple
# Default: GC-managed allocation
val player = Player { name: "Hero", hp: 100 }
val copy = player    # GC handles sharing
```

- Values allocated via `GcAllocator`
- Tracing via Abfall backend
- Non-deterministic finalization
- CLI: `--gc=on` (default)

---

## Manual Domain (Opt-in)

### Unique Pointer (`&T`)

```simple
# Single owner, RAII
val owner: &Data = new(&) Data(42)
val moved = move owner    # Explicit transfer
# owner is now invalid
```

- Exactly one owner at a time
- Move-only (no implicit copy)
- Freed deterministically at scope end

### Shared Pointer (`*T`)

```simple
# Reference counted, read-only
val shared1: *Data = new* Data(42)
val shared2 = shared1    # Refcount incremented

# Mutation via COW pattern
val updated = shared1.with_value(100)
```

- Multiple owners via refcount
- Read-only in safe code
- COW for updates (returns new `*T`)

### Weak Pointer (`-T`)

```simple
# Non-owning, breaks cycles
val shared: *Node = new* Node(1)
val weak: -Node = weak_of(shared)

match weak.upgrade():
    case Some(strong): use(strong)
    case None: log "Node freed"
```

- Does not keep object alive
- Must upgrade before use
- Returns `Option<*T>`

### Handle Pointer (`+T`)

```simple
# Pool-managed, slot + generation
handle_pool Enemy:
    capacity: 1024

val h: +Enemy = new+ Enemy(hp: 100)
match Enemy.handle_get_mut(h):
    case Some(e): e.hp -= 10
    case None: log "Invalid handle"
```

- Lightweight ID into global pool
- Generation validates stale handles
- Ideal for entity systems

---

## Domain Interop

**Explicit conversions required:**

```simple
# GC -> Manual
val gc_val: Data = Data(42)
val unique: &Data = clone_unique(gc_val)
val shared: *Data = clone_shared(gc_val)

# Manual -> GC
val manual: &Data = new(&) Data(42)
val gc_val: Data = into_gc(move manual)
```

- No implicit mixing between domains
- Compiler enforces explicit conversions
- Type checker validates pointer kinds

---

## Safety Rules

### Rule 1: No Shared Mutation

```simple
val shared: *Data = new* Data(0)
# shared.value = 10        # Error: shared mutation
val updated = shared.with_value(10)  # OK: COW
```

### Rule 2: No Implicit Unique Copy

```simple
val unique: &Box = new(&) Box(42)
# val copy = unique        # Error: implicit copy
val moved = move unique    # OK: explicit move
val cloned = unique.clone()  # OK: explicit clone
```

### Rule 3: No Escaping Borrows

```simple
fn bad() -> &Data:
    val local: &Data = new(&) Data(42)
    return local           # Error: escapes scope

fn good() -> Data:
    val local: &Data = new(&) Data(42)
    return move local      # OK: ownership transfer
```

### Rule 4: Mut Requires Exclusive Access

```simple
fn update(data: mut Data):   # Exclusive access
    data.value = 10          # OK

fn read(data: Data):         # Shared access
    # data.value = 10        # Error: no mut
```

### Rule 5: Isolated Requires No Aliases

```simple
fn bad(data: ~Data):
    val copy = data        # Error: iso can't be aliased
    pass

fn good(data: ~Data):
    val moved = move data  # OK: ownership transfer
    pass
```

---

## Implementation

### Layout/ABI

- **`common::gc`**: `GcAllocator`, `GcHandle<T>`, `GcRoot`
- **`common::manual`**: `Unique<T>`, `Shared<T>`, `WeakPtr<T>`, `HandlePool`, `Handle<T>`
- **`runtime::memory`**: `gc` (Abfall), `no_gc` (boxed, no collection)

### Compiler Lowering

| Type | Lowering |
|------|----------|
| `T` | `GcAllocator::alloc_bytes` |
| `&T` | Stack/heap malloc + RAII drop |
| `*T` | `Rc<T>` (refcounted struct) |
| `@T` | `Arc<T>` (atomic refcount, thread-safe) |
| `~T` | Capability marker (compile-time, erased) |
| `-T` | Weak refcount |
| `+T` | Pool slot + generation |

---

## Migration (Phased)

See `doc/plan/manual_memory_safety_plan.md` for details.

| Phase | Goal | Status |
|-------|------|--------|
| 1. Warnings | Identify violations | In Progress |
| 2. Refactor | Fix all warnings | Planned |
| 3. Strict | Default strict mode | Planned |
| 4. Legacy | Deprecated escape | Planned |

---

## Testing

```bash
# GC logs
simple run --gc-log script.spl

# Memory warnings
simple check --memory-warnings src/

# Debug lifecycle
simple run --debug-lifecycle script.spl

# Debug refcount
simple run --debug-rc script.spl
```

---

## Related Documents

- **Plan:** `doc/plan/manual_memory_safety_plan.md`
- **Architecture:** `doc/architecture/memory_model_implementation.md`
- **Spec:** `doc/spec/generated/memory.md`
- **Tests:** `simple/std_lib/test/features/types/memory_safety_spec.spl`

---

## Lean Verification (TODO)

### Isolated Capability Verification

- [ ] **Aliasing Invariant**: Prove `iso T` values have exactly one owner
- [ ] **Transfer Safety**: Prove `move` transfers preserve isolation
- [ ] **Downgrade Correctness**: Prove `iso -> mut -> imm` preserves safety
- [ ] **Actor Message Safety**: Prove actor messages with `iso` are data-race free
- [ ] **No Upgrade**: Prove `imm -> iso` and `mut -> iso` are impossible

### Arc Verification

- [ ] **Atomic Refcount**: Prove refcount operations are atomic
- [ ] **Thread Safety**: Prove `@T` can be safely shared across threads
- [ ] **Weak Upgrade**: Prove weak upgrade is atomic and safe

See `doc/todo/lean_iso_verification.md` for detailed proof obligations.
