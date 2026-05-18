# FFI → SFFI Full Rename

## Goal
Rename all `ffi` references to `sffi` across the entire codebase (namespace, files, identifiers, comments). Profile perf/binary size to ensure no regression. Add compiler guard to reject `std.ffi`.

## Acceptance Criteria
- AC-1: No `use std.ffi.*` imports remain (all → `use std.sffi.*`)
- AC-2: No files named `*ffi*` remain (renamed to `*sffi*`)
- AC-3: No identifiers/variables named `*ffi*` in Simple source (→ `*sffi*`)
- AC-4: Comments/docs updated
- AC-5: Compiler/interpreter rejects `std.ffi` with helpful error
- AC-6: Perf equal or better (measured before/after)
- AC-7: Binary size equal or better
- AC-8: JIT and optimization plugins updated
- AC-9: All tests pass after rename

## Milestones
1. [x] Baseline perf/size capture
2. [ ] Library namespace rename (`src/lib/nogc_sync_mut/ffi/` → `sffi/`)
3. [ ] Compiler backend file renames
4. [ ] App/tool file renames
5. [ ] Identifier/class/variable renames
6. [ ] Comments and docs
7. [ ] Compiler guard (reject `std.ffi`)
8. [ ] JIT/optimization plugin updates
9. [ ] Final perf/size verification

## Phase
Phase 5 (implement) — executing bulk rename
