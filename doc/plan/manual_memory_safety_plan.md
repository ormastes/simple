# Manual Memory Safety Plan (Simple)

> **Version:** 2.0 (Simplified)
> **Last Updated:** 2026-01-19
> **Status:** In Progress

## Overview

This plan provides a **phased migration** from permissive memory handling to strict memory safety. The approach is:

1. **Add Warnings** → Identify violations without breaking code
2. **Refactor Code** → Fix all warnings in the codebase
3. **Enable Strict Mode** → Make strict the default (zero warnings)
4. **Legacy Mode** → Deprecated escape hatch for old code

---

## Pointer Types (Quick Reference)

| Syntax | Name | Ownership | Mutation | Use Case |
|--------|------|-----------|----------|----------|
| `T` | GC Reference | GC-managed | Via `mut` | Default (most code) |
| `&T` | Unique | Single owner | Via `mut` | RAII, exclusive access |
| `*T` | Shared | Ref-counted | Read-only | Multiple owners |
| `-T` | Weak | Non-owning | N/A | Break cycles |
| `+T` | Handle | Pool-managed | Via pool | Entity systems |

**Capabilities (existing):**
| Syntax | Name | Aliasing |
|--------|------|----------|
| `T` | Shared | Multiple readers OK |
| `mut T` | Exclusive | Single writer only |
| `iso T` | Isolated | No aliasing, transferable |

---

## Phase 1: Warnings (Current)

**Goal:** Emit warnings for all memory safety violations without breaking existing code.

### Warning Codes

| Code | Description | Suggested Fix |
|------|-------------|---------------|
| `W1001` | Shared pointer mutation | Use `into_unique()` or COW pattern |
| `W1002` | Unique pointer copied | Use explicit `clone()` or `share()` |
| `W1003` | Mutable var with shared type | Remove `var` or use unique pointer |
| `W1004` | Borrow escapes scope | Return owned value instead |
| `W1005` | Potential cycle in RC graph | Add weak pointer (`-T`) |
| `W1006` | Missing `mut` for mutation | Add `mut` capability |

### CLI Flags

```bash
# Show memory warnings (default in legacy mode)
simple check --memory-warnings src/

# Treat warnings as errors (strict mode preview)
simple check --memory-warnings --Werror src/

# Count warnings only
simple check --memory-warnings --count src/
```

### Implementation

```rust
// In compiler/src/hir/lower/memory_check.rs
pub enum MemoryWarning {
    SharedMutation { span: Span, suggested_fix: String },
    UniqueCopied { span: Span, suggested_fix: String },
    MutableShared { span: Span },
    BorrowEscapes { span: Span, owner_scope: Span },
    PotentialCycle { span: Span, types: Vec<TypeId> },
    MissingMut { span: Span },
}
```

---

## Phase 2: Refactor Existing Code

**Goal:** Fix all memory warnings in codebase before enabling strict mode.

### Refactor Priority

1. **Core stdlib** (`simple/std_lib/src/core_nogc/`)
2. **Host modules** (`simple/std_lib/src/host/`)
3. **GPU modules** (`simple/std_lib/src/gpu/`)
4. **Apps and tests** (`simple/app/`, `test/`)

### Common Patterns

**Before (Warning W1001):**
```simple
val shared: *Data = new* Data(value: 0)
shared.value = 10  # W1001: Shared pointer mutation
```

**After:**
```simple
val shared: *Data = new* Data(value: 0)
val updated: *Data = shared.with_value(10)  # COW pattern
```

**Before (Warning W1002):**
```simple
val unique: &Box = new(&) Box(42)
val copy = unique  # W1002: Unique pointer copied
```

**After:**
```simple
val unique: &Box = new(&) Box(42)
val moved = move unique      # Explicit move
# OR
val cloned = unique.clone()  # Explicit clone
```

---

## Phase 3: Strict Mode Default

**Goal:** When all warnings are fixed, make strict mode the default.

### Strict Mode Rules

1. **No implicit unique copies** → Must use `move` or `clone()`
2. **No shared mutation** → Must use COW or `into_unique()`
3. **No `var *T`** → Shared pointers are immutable bindings
4. **No escaping borrows** → Checked at compile time
5. **Explicit domain conversions** → GC ↔ Manual requires builtins

### CLI

```bash
# Strict mode (default after migration)
simple check src/

# Explicit strict mode
simple check --memory-mode=strict src/
```

---

## Phase 4: Legacy Mode (Deprecated)

**Goal:** Escape hatch for old code that cannot be migrated.

### Usage

```simple
#[memory_mode(legacy)]
module old_code:
    # Warnings only, not errors
    fn unsafe_pattern():
        val shared: *Data = new* Data(0)
        shared.value = 10  # Warning, not error
```

### CLI Override

```bash
# Force legacy mode globally
simple check --memory-mode=legacy src/
```

### Deprecation Timeline

| Version | Legacy Mode Status |
|---------|-------------------|
| v0.9 | Available, warnings emitted |
| v1.0 | Deprecated, loud warnings |
| v2.0 | Removed |

---

## Core Rules (Simplified)

### Rule 1: Ownership

```simple
# Unique: exactly one owner, move-only
val owner: &Data = new(&) Data(42)
val new_owner = move owner    # OK: explicit move
# val copy = owner            # Error: implicit copy

# Shared: multiple owners, copyable
val shared1: *Data = new* Data(42)
val shared2 = shared1         # OK: refcount incremented
```

### Rule 2: Mutation

```simple
# Mutation requires mut capability
fn update(data: mut Data):    # Exclusive access
    data.value = 10           # OK

fn read(data: Data):          # Shared access
    # data.value = 10         # Error: no mut

# Shared pointers: use COW
val shared: *List<i32> = new* [1, 2, 3]
val updated = shared.appended(4)  # Returns new *List<i32>
```

### Rule 3: Lifetimes (Implicit)

```simple
# Borrows cannot escape their owner's scope
fn bad() -> &Data:
    val local: &Data = new(&) Data(42)
    return local  # Error W1004: borrow escapes scope

fn good() -> Data:
    val local: &Data = new(&) Data(42)
    return move local  # OK: ownership transferred
```

### Rule 4: Cycles

```simple
# Shared pointers can create cycles (leak)
struct Node:
    next: *Node  # Warning W1005 if forms cycle

# Use weak pointers to break cycles
struct SafeNode:
    next: -Node  # Weak reference, no leak
```

---

## Debug Tracing

```bash
# Show lifecycle operations
simple run --debug-lifecycle script.spl

# Show refcount changes
simple run --debug-rc script.spl

# Show COW operations
simple run --debug-cow script.spl
```

**Output format:**
```
[MOVE]   main.spl:12:5  &Data     # ownership transferred
[DROP]   main.spl:20:1  &Data     # freed at scope end
[RC_INC] main.spl:15:9  *List     # copy incremented refcount
[RC_DEC] main.spl:25:1  *List     # scope exit decremented
[COW]    main.spl:18:5  *List     # clone-on-write triggered
```

---

## Error Codes (Strict Mode)

| Code | Description |
|------|-------------|
| `E1001` | Shared pointer mutation without COW |
| `E1002` | Implicit copy of unique pointer |
| `E1003` | Mutable binding of shared pointer |
| `E1004` | Borrow escapes owner scope |
| `E1005` | Reference cycle without weak pointer |
| `E1006` | Mutation without `mut` capability |
| `E1007` | Implicit GC/manual domain conversion |

---

## Migration Checklist

### For Library Authors

- [ ] Run `simple check --memory-warnings` on all code
- [ ] Fix all W1001-W1006 warnings
- [ ] Add explicit `move` for ownership transfers
- [ ] Use COW patterns for shared mutation
- [ ] Add weak pointers for cyclic structures
- [ ] Test with `--memory-mode=strict`

### For App Developers

- [ ] Update dependencies to strict-compatible versions
- [ ] Run `simple check --memory-warnings`
- [ ] Fix warnings in application code
- [ ] Remove `#[memory_mode(legacy)]` annotations
- [ ] Test with `--memory-mode=strict`

---

## Implementation Status

| Component | Warnings | Strict | Notes |
|-----------|----------|--------|-------|
| Parser/AST | ✅ | ✅ | Pointer kinds parsed |
| Type system | ✅ | 🔄 | Capabilities done, ownership WIP |
| Type checker | 🔄 | ⏳ | Warning emission in progress |
| MIR passes | ⏳ | ⏳ | Lifecycle lowering planned |
| Interpreter | ✅ | 🔄 | Debug checks available |
| Stdlib | ⏳ | ⏳ | Refactoring planned |

Legend: ✅ Complete | 🔄 In Progress | ⏳ Planned

---

## Related Documents

- **Design:** `doc/design/memory.md`
- **Architecture:** `doc/architecture/memory_model_implementation.md`
- **Spec:** `doc/spec/generated/memory.md`
- **Tests:** `simple/std_lib/test/features/types/memory_types_spec.spl`
- **Tests:** `simple/std_lib/test/features/types/borrowing_spec.spl`
