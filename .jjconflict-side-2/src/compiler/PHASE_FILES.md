# Phase Files - Consolidation Complete

**Status:** Consolidated (2026-02-21); orphans removed (2026-08-05)

---

## What Happened

Phase files documented the step-by-step implementation of advanced compiler features.
They have been **consolidated** into single files per feature, removing ~8K lines of duplication.

---

## Consolidated Files

| Feature | Old Phase Files | New File | Location |
|---------|----------------|----------|----------|
| Bidirectional Type Checking | `bidir_phase1a-d.spl` (4 files, removed) | `bidirectional_checking.spl` | `30.types/` |
| Higher-Rank Polymorphism | `higher_rank_poly_phase5b.spl` (1 file remains; 5a/5c/5d removed 2026-08-05) | `higher_rank_poly.spl` | `30.types/` |
| Variance Checking | `variance_phase6a.spl` (1 file remains; 6b/6c/6d removed 2026-08-05) | `variance.spl` / `variance_types.spl` | `30.types/` |
| Const Generics | `const_keys_phase8a.spl` (1 file remains; 8b/8c removed 2026-08-05) | `const_keys.spl` | `30.types/` |
| SIMD Intrinsics | `simd_phase9a-c.spl` (3 files) | `simd.spl` | `30.types/` |
| Effects | `effects_phase3a.spl` (1 file) | `effects.spl` (already existed) | `00.common/` |

`associated_types_phase4a-d.spl` (4 files) and `macro_checker_phase7a-c.spl` (3 files) have
been fully removed — all superseded by `associated_types.spl` and `macro_checker.spl`
respectively, with zero remaining importers.

**Total:** 26 phase files → 19 removed (4 bidir + 4 associated_types + 3 macro_checker +
3 higher_rank_poly + 3 variance + 2 const_keys), 7 remain (1 higher_rank_poly + 1 variance +
1 const_keys + 3 simd + 1 effects) pending further cleanup.

---

## Archived Originals

All original phase files (including the 15 removed 2026-08-05) are preserved in
`doc/05_design/compiler/phases/` for historical reference.

---

## Related Documentation

- `DESUGARING_PLAN.md` - How Full Simple → Core Simple transformation works
- `src/compiler/README.md` - Compiler architecture overview
