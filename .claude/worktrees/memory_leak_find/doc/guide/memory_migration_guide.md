# Memory Safety Migration Guide

> **Version:** 1.0
> **Last Updated:** 2026-01-19
> **For:** Simple v0.9+

## Quick Start

```bash
# Check your code for memory warnings
simple check --memory-warnings src/

# Preview strict mode
simple check --memory-warnings --Werror src/

# Run with legacy mode (temporary)
simple run --memory-mode=legacy script.spl
```

---

## Migration Phases

```
┌─────────────────────────────────────────────────────────────┐
│                    Migration Timeline                        │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  Phase 1         Phase 2         Phase 3         Phase 4    │
│  Warnings ──────► Refactor ─────► Strict ────────► Legacy   │
│  (Current)        (Next)          (Default)       (Removed) │
│                                                              │
│  v0.9            v0.10           v1.0            v2.0       │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

---

## Phase 1: Warnings (Current - v0.9)

**Goal:** Identify all memory safety violations without breaking existing code.

### What Happens

- Compiler emits warnings for unsafe patterns
- Code continues to compile and run
- Warnings include suggested fixes

### Warning Codes

| Code | Pattern | Fix |
|------|---------|-----|
| W1001 | Shared pointer mutation | Use COW pattern |
| W1002 | Unique pointer copied | Use `move` or `clone()` |
| W1003 | `var *T` declaration | Use `val *T` |
| W1004 | Borrow escapes scope | Return owned value |
| W1005 | RC cycle detected | Add weak pointer (`-T`) |
| W1006 | Mutation without `mut` | Add `mut` capability |

### Action Required

Run the warning check and note all violations:

```bash
simple check --memory-warnings src/
```

Example output:
```
src/game/player.spl:42:5: warning[W1001]: Shared pointer mutation
  --> shared.hp = 100
  help: Use COW pattern: `val updated = shared.with_hp(100)`

src/game/entity.spl:15:3: warning[W1002]: Implicit copy of unique pointer
  --> val copy = unique_entity
  help: Use explicit `move unique_entity` or `unique_entity.clone()`
```

---

## Phase 2: Refactor (v0.10)

**Goal:** Fix all warnings in your codebase.

### Common Refactoring Patterns

#### W1001: Shared Pointer Mutation

**Before:**
```simple
val shared: *Config = new* Config(value: 0)
shared.value = 10  # Warning: shared mutation
```

**After (COW pattern):**
```simple
val shared: *Config = new* Config(value: 0)
val updated = shared.with_value(10)  # Returns new *Config
```

**After (Builder method):**
```simple
impl Config:
    fn with_value(self, v: i64) -> *Config:
        return new* Config(value: v)
```

---

#### W1002: Unique Pointer Copied

**Before:**
```simple
val unique: &Box = new(&) Box(42)
val copy = unique  # Warning: implicit copy
use(unique)        # Error: use after move
```

**After (Explicit move):**
```simple
val unique: &Box = new(&) Box(42)
val moved = move unique  # Explicit transfer
# unique is now invalid
```

**After (Explicit clone):**
```simple
val unique: &Box = new(&) Box(42)
val cloned = unique.clone()  # New instance
use(unique)                   # OK: still valid
```

---

#### W1003: Mutable Shared Binding

**Before:**
```simple
var shared: *Data = new* Data(0)  # Warning: var *T
shared = new* Data(1)             # Reassignment
```

**After:**
```simple
val shared1: *Data = new* Data(0)
val shared2: *Data = new* Data(1)  # Separate bindings
```

---

#### W1004: Escaping Borrow

**Before:**
```simple
fn bad() -> &Data:
    val local: &Data = new(&) Data(42)
    return local  # Warning: escapes scope
```

**After:**
```simple
fn good() -> Data:
    val local: &Data = new(&) Data(42)
    return move local  # Transfer ownership
```

---

#### W1005: Reference Cycle

**Before:**
```simple
struct Node:
    next: *Node  # Warning: potential cycle
```

**After:**
```simple
struct Node:
    next: -Node  # Weak pointer breaks cycle
```

---

#### W1006: Missing Mut

**Before:**
```simple
fn update(data: Data):
    data.value = 10  # Warning: mutation without mut
```

**After:**
```simple
fn update(data: mut Data):  # Explicit mut
    data.value = 10         # OK
```

---

## Phase 3: Strict Mode (v1.0)

**Goal:** Strict mode becomes the default.

### What Changes

- All warnings become errors
- Legacy mode still available (with deprecation warning)
- No code changes if Phase 2 complete

### Verification

```bash
# Should have zero warnings
simple check --memory-warnings src/

# Test strict mode explicitly
simple check --memory-mode=strict src/
```

---

## Phase 4: Legacy Mode Removal (v2.0)

**Goal:** Remove legacy mode entirely.

### What Changes

- Legacy mode no longer available
- All code must be strict-compatible
- Migration complete

---

## Checklist

### For Library Authors

- [ ] Run `simple check --memory-warnings` on all code
- [ ] Fix all W1001-W1006 warnings
- [ ] Add `move` for ownership transfers
- [ ] Use COW for shared mutation
- [ ] Add weak pointers for cycles
- [ ] Test with `--memory-mode=strict`
- [ ] Update documentation
- [ ] Publish strict-compatible version

### For Application Developers

- [ ] Update dependencies to strict versions
- [ ] Run `simple check --memory-warnings`
- [ ] Fix warnings in application code
- [ ] Remove `#[memory_mode(legacy)]` if used
- [ ] Test with `--memory-mode=strict`
- [ ] Deploy with strict mode

---

## Troubleshooting

### "Too many warnings"

Start with one module at a time:
```bash
simple check --memory-warnings src/compiler_core/
```

### "Can't use COW, need mutation"

Use unique pointer instead:
```simple
# Instead of *Data, use &Data for mutation
val unique: &Data = new(&) Data(0)
unique.value = 10  # OK with mut
```

### "Need shared AND mutable"

Use interior mutability pattern:
```simple
struct SharedMut:
    inner: &mut Data  # Unique mutable inside shared

fn update(s: *SharedMut):
    s.inner.value = 10  # Exclusive access to inner
```

### "Legacy code too complex to migrate"

Use legacy annotation temporarily:
```simple
#[memory_mode(legacy)]
module legacy_code:
    # Old code with warnings
```

---

## Related Documents

- **Plan:** `doc/plan/manual_memory_safety_plan.md`
- **Design:** `doc/design/memory.md`
- **Spec:** `simple/std_lib/test/features/types/memory_safety_spec.spl`
