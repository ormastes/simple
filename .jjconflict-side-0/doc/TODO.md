# TODO List

**Generated:** 2026-05-10
**Total:** 0 items | **Open:** 0 | **Blocked:** 0 | **Stale:** 0
**Database:** `doc/todo/todo_db.sdn`

## Statistics

### By Area

| Area | Count | P0 | P1 | P2 | P3 | Blocked |
|------|-------|----|----|----|----|---------|

### By Priority

| Priority | Count | Open | Blocked | Stale |
|----------|-------|------|---------|-------|
| P0 (critical) | 0 | 0 | 0 | 0 |
| P1 (high) | 0 | 0 | 0 | 0 |
| P2 (medium) | 0 | 0 | 0 | 0 |
| P3 (low) | 0 | 0 | 0 | 0 |

## Feature Requests

### FR-INTERP-001: `me fn` nested mutation loss

**ID:** FR-INTERP-001
**Area:** compiler (interpreter)
**Priority:** P1 (high)
**Status:** Open

When a method on `self` calls another method on `self` (nested `me fn` calls), the outer method's mutations to `self` fields are lost. The inner call snapshots and restores `self`, overwriting the caller's in-progress mutations. This blocks full RamFS/NVFS API benchmarking — inode push operations inside driver methods are silently discarded.

**Workaround:** Extract mutations to module-level helper functions that take the struct by value and return the updated copy.

**Blocks:** Full FS driver API benchmarking (AC-1 of fs-opt-general).

---

### FR-INTERP-002: Deeply nested field assignment (3+ levels)

**ID:** FR-INTERP-002
**Area:** compiler (interpreter)
**Priority:** P1 (high)
**Status:** Open

Assignment to deeply nested fields (`self.arr[i].field.subfield = x`) is rejected or silently discarded by the interpreter. The pattern appears in inode and extent-map struct updates across NVFS, DBFS, and RamFS. The interpreter handles 1-level field assignment (`self.field = x`) but fails on 2+ levels through an indexed element.

**Workaround:** Use intermediate variables: `var tmp = self.arr[i]; tmp.field.subfield = x; self.arr[i] = tmp` — but this pattern itself may also trigger the me-fn mutation loss (FR-INTERP-001).

**Blocks:** Full FS driver struct-of-struct mutation in interpreter mode.

---

## Appendix

### Legend

- **P0/critical:** Blocking, fix immediately
- **P1/high:** Important, next sprint
- **P2/medium:** Should do, backlog
- **P3/low:** Nice to have, someday

### Areas

- `runtime` - GC, values, monoio, concurrency
- `codegen` - MIR, Cranelift, LLVM, Vulkan
- `compiler` - HIR, pipeline, interpreter
- `parser` - Lexer, AST, parsing
- `type` - Type checker, inference
- `stdlib` - Simple standard library
- `gpu` - GPU/SIMD/graphics
- `ui` - UI framework
- `test` - Test frameworks
- `driver` - CLI, tools
- `loader` - SMF loader
- `pkg` - Package manager
- `doc` - Documentation, specs, guides
