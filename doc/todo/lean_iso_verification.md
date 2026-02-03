# Lean Verification: Isolated Capability

## Overview

Formal verification of `iso T` (isolated capability) in Lean 4.

## Proof Obligations

### 1. Aliasing Invariant
```lean
theorem iso_no_alias (x : iso T) :
  forall y : T, y ≠ x.value → no_alias x y
```

### 2. Transfer Preserves Isolation
```lean
theorem move_preserves_iso (x : iso T) :
  let y = move x in
  invalidated x ∧ isolated y
```

### 3. Downgrade Safety
```lean
theorem iso_to_mut_safe (x : iso T) :
  let y : mut T = downgrade x in
  exclusive_access y
```

### 4. Actor Safety
```lean
theorem actor_message_safe (msg : iso T) (actor : Actor) :
  send actor msg → no_data_race
```

## Implementation Status

- [ ] Define `iso` type in Lean
- [ ] Implement aliasing checker
- [ ] Prove transfer theorems
- [ ] Integrate with Simple compiler

## Related

- `doc/design/memory.md` - Memory model design
- `src/std/type/lean_types.spl` - Lean type generation
- `test/lib/std/unit/verification/memory_capabilities_spec.spl` - Test specs
