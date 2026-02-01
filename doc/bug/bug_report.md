# Bug Report

## Open Bugs

(none)

## Closed Bugs

### BUG-1: Test context performance O(n²) [P1] - FIXED
- **Area**: spec_framework
- **Status**: fixed
- **File**: `rust/compiler/src/interpreter_call/bdd.rs`

**Description**: Test execution time grew exponentially with number of context blocks.

**Root cause**: Hook collection walked the parent chain for every `it` block without caching.

**Fix**: Hook caching indexed by stack depth in `bdd.rs:209-260` (`get_before_each_hooks_cached()` / `get_after_each_hooks_cached()`). Cache invalidated on context entry/exit and hook addition.

**Verification** (2026-02-01):

| Contexts | Before fix | After fix |
|----------|-----------|-----------|
| 4 nested | 9.6s | 5ms |
| 8 nested | 23.6s | 3ms |
| 10 nested + before_each | timeout | 2ms |
| 16 sibling | timeout | 3ms |

`tooling_spec.spl` (10 contexts, 28 tests): 3ms. `set_spec.spl` no longer times out (had separate compile error, now fixed).

---
*Generated: 2026-01-28, Closed: 2026-02-01*
