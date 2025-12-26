# Documentation Archive

This directory contains historical, outdated, or superseded documentation files.

## Why Archive?

Documents are archived when:
1. **Superseded:** Newer, better documentation exists elsewhere
2. **Historical:** Captures a milestone but no longer current
3. **Outdated:** Information is no longer accurate
4. **Consolidated:** Content merged into a single source of truth

## Archived Documents

### JJ Integration (Superseded)
- `jj_integration_plan.md` - Old plan → **See:** `doc/plans/27_jj_integration.md`
- `jj_phase1_2_complete.md` - Phase 1-2 completion notes
- `jj_usage.md` - Old usage guide → **See:** `doc/plans/27_jj_integration.md`

**Status:** JJ integration is 67% complete. See current docs in `doc/plans/27_jj_integration.md`

### LLVM Backend (Historical)
- `LLVM_ACHIEVEMENT.md` - LLVM backend milestone announcement
- `llvm_implementation_complete.md` - Implementation completion notes

**Status:** LLVM backend is complete and documented in `doc/llvm_backend.md`

### Doctest (Superseded)
- `sdoctest_implementation.md` - Initial implementation notes
- `sdoctest_session_summary.md` - Session summary
- `sdoctest_sprint2_final.md` - Sprint 2 completion
- `sdoctest_sprint2_progress.md` - Sprint 2 early progress
- `doctest_integration.md` - Old integration notes

**Status:** Doctest is 90% complete. See:
- Current status: `doc/status/sdoctest.md`
- Implementation plan: `doc/plans/29_doctest.md`
- Specification: `doc/spec/sdoctest.md`

### Outdated/Temporary
- `32bit_support.md` - 32-bit support notes (deferred - needs LLVM)
- `temp_stdlib_inconsistencies.md` - Temporary stdlib tracking (being addressed)

## Finding Current Documentation

If you're looking for archived content, check:

| Archived Topic | Current Location |
|----------------|------------------|
| JJ Integration | `doc/plans/27_jj_integration.md` |
| LLVM Backend | `doc/llvm_backend.md` |
| Doctest Status | `doc/status/sdoctest.md` |
| Doctest Plan | `doc/plans/29_doctest.md` |
| Doctest Spec | `doc/spec/sdoctest.md` |
| 32-bit Support | `doc/features/feature.md` (#220, deferred) |

## Archive Policy

Documents should be moved to archive/ when:
- ✅ Content has been integrated into current docs
- ✅ Historical value for reference but not current
- ✅ Superseded by better organization elsewhere

Documents should **not** be deleted because:
- 🔍 Historical context is valuable
- 📊 Track project evolution
- 🔗 External links may reference them
- 📚 Learning from past decisions

## See Also

- `doc/README.md` - Main documentation index
- `doc/features/feature.md` - Current feature status
- `doc/plans/` - Active implementation plans
- `doc/status/` - Feature implementation tracking
