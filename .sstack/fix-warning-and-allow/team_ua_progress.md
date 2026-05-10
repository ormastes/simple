# Team U-A Progress — fix-warning-and-allow (REQ-3 Tier A)

## Batch 1 — All 158 files (single batch run)

**Date:** 2026-04-28
**Files touched:** 158 / 158
**Commit hash:** 21647dacf1
**Verification:** no `@allow(unnamed_duplicate_typed_args)` or `#![allow(unnamed_duplicate_typed_args)]` remain in any tier_a file
**Reclassified to Tier B:** 0

### Approach
- Removed both `#![allow(unnamed_duplicate_typed_args)]` (line 1) and `@allow(unnamed_duplicate_typed_args)` (line 2) from all 158 files.
- Added `// reason: positional <module> API` comment on the line immediately above each `fn` definition whose parameter list contains ≥2 parameters sharing the same type.
- Module label derived from path: strip `src/lib/`, drop category prefixes (`common`, `nogc_sync_mut`, `gc_async_mut`, `nogc_async_mut`, `nogc_async_mut_noalloc`), join remaining path components.

### Lint check after transformation
- `unnamed_duplicate_typed_args` warnings in lint output are all from files OUTSIDE tier_a scope (compiler/70.backend/, compiler/35.semantics/, etc.) — pre-existing, not introduced by this change.
- Zero tier_a files emit `unnamed_duplicate_typed_args` warnings after transformation.

### Files processed
All 158 files from `.sstack/fix-warning-and-allow/tier_a_files.txt`.
