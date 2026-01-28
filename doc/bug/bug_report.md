# Bug Report

## Open Bugs

### BUG-1: Test context performance O(n²) [P1]
- **Area**: spec_framework
- **Status**: open
- **File**: `src/lib/std/src/spec/`

**Description**: Test execution time grows exponentially with number of context blocks.

| Contexts | Duration |
|----------|----------|
| 4 | 9.6s |
| 6 | 11.6s |
| 7 | 15.8s |
| 8 | 23.6s |

Tests with 10+ contexts timeout (>120s). Examples:
- `set_spec.spl` (16 contexts) - times out
- `tooling_spec.spl` (10 contexts) - times out

**Reproducible by**: `loops_8ctx2_spec.spl` in scratchpad

---
*Generated: 2026-01-28*
