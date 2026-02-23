# Phase Files - Consolidation Complete

**Status:** Consolidated (2026-02-21)

---

## What Happened

Phase files documented the step-by-step implementation of advanced compiler features.
They have been **consolidated** into single files per feature, removing ~8K lines of duplication.

---

## Consolidated Files

| Feature | Old Phase Files | New File | Location |
|---------|----------------|----------|----------|
| Bidirectional Type Checking | `bidir_phase1a-d.spl` (4 files) | `bidirectional_checking.spl` | `30.types/` |
| Associated Types | `associated_types_phase4a-d.spl` (4 files) | `associated_types.spl` | `30.types/` |
| Higher-Rank Polymorphism | `higher_rank_poly_phase5a-d.spl` (4 files) | `higher_rank_poly.spl` | `30.types/` |
| Variance Checking | `variance_phase6a-d.spl` (4 files) | `variance.spl` | `30.types/` |
| Macro Hygiene | `macro_checker_phase7a-c.spl` (3 files) | `macro_checker.spl` | `30.types/` |
| Const Generics | `const_keys_phase8a-c.spl` (3 files) | `const_keys.spl` | `30.types/` |
| SIMD Intrinsics | `simd_phase9a-c.spl` (3 files) | `simd.spl` | `30.types/` |
| Effects | `effects_phase3a.spl` (1 file) | `effects.spl` (already existed) | `00.common/` |

**Total:** 26 phase files → 7 consolidated files + 1 existing

---

## Archived Originals

All original phase files are preserved in `doc/design/phases/` for historical reference.

---

## Related Documentation

- `DESUGARING_PLAN.md` - How Full Simple → Core Simple transformation works
- `src/compiler/README.md` - Compiler architecture overview
