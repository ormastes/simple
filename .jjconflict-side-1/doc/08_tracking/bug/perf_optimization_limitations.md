# Performance Optimization — Known Limitations

**Date:** 2026-04-06
**Feature:** perf_optimization

## Limitations

### L-001: PersistentDict hash relies on text interpolation
- **Impact:** Medium
- **Description:** `pd_hash_key()` converts keys to text via `"{key}"` then hashes. Two distinct objects with identical text representations will hash identically (correct but slower for custom types).
- **Workaround:** Use types with unique text representations as keys.
- **Fix:** Integrate Hash trait directly when PersistentDict gains generics.

### L-002: PersistentVec chunk boundary overhead
- **Impact:** Low
- **Description:** `from_array()` with exactly 32n elements creates n full chunks. Subsequent push creates a new chunk for 1 element. Normal usage not affected.
- **Workaround:** None needed — only affects construction pattern.

### L-003: LOAD_FAST not integrated
- **Impact:** High (deferred)
- **Description:** String interning pool (`intern.spl`) created but not wired into `env.spl`/`eval.spl`. Variable lookup still uses scope chain walking with string comparison.
- **Workaround:** FNV-1a hash function upgrade reduces collision chains (~2-3x improvement).
- **Fix:** Requires parser changes to assign compile-time local indices + env.spl fast path.

### L-004: TCO limited to direct self-recursion
- **Impact:** Low
- **Description:** TCO pass only handles functions calling themselves directly. Mutual recursion (A calls B calls A) is not optimized.
- **Workaround:** Manually convert mutual recursion to loop + state machine.

### L-005: GVN does not handle stores/loads
- **Impact:** Low
- **Description:** GVN only value-numbers pure expressions (BinOp, UnaryOp, GetField, Cast). Memory operations (Load, Store) are treated as opaque.
- **Workaround:** CSE pass handles some local redundancy for loads.

### L-006: Cross-session bytecode cache not implemented
- **Impact:** Medium (deferred)
- **Description:** Module loader has in-session mmap cache but no persistent .splc bytecode cache across interpreter restarts.
- **Workaround:** SMF cache covers compiled-mode. Only interpreter mode re-parses on restart.
