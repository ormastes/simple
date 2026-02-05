# Database Consolidation - Executive Summary

**Date:** 2026-02-05
**Objective:** Migrate test runner from custom database implementations to unified library

---

## Quick Facts

| Metric | Value |
|--------|-------|
| **Code to Delete** | ~1,292 lines |
| **Files to Delete** | 5 files |
| **Estimated Effort** | 10-15 hours (dev) + 5-8 hours (testing) |
| **Timeline** | 2-4 days |
| **Risk Level** | Medium (well-tested migration path) |

---

## What's Duplicated?

### Test Database (`test_db_*.spl` → `lib/database/test.spl`)

**Custom Implementation Has:**
- StringInterner integration
- File/suite/test registry
- Flaky test detection (flaky_count, last_10_runs)
- Statistical analysis (p50, p90, p95, p99, IQR)
- Outlier detection
- Baseline tracking with auto-updates
- Change event tracking
- Timing runs history
- Run management (start/complete/cleanup/prune)
- Dual-file storage (stable + volatile)

**Unified Library Has:**
- Basic run tracking
- Basic result storage
- Generic SdnDatabase backend

**Missing in Unified:** Everything except the basics (need to add ~10 methods)

---

### Feature Database (`feature_db.spl` → `lib/database/feature.spl`)

**Custom Implementation Has:**
- 4 execution modes (interpreter, jit, smf_cranelift, smf_llvm)
- SSpec metadata parsing (`#[id(...)]`, `#[modes(...)]`)
- Category extraction from paths
- Duplicate detection
- Semantic ID sorting ("1.2" < "1.10")
- Orphaned feature detection
- CSV parsing with quote support

**Unified Library Has:**
- 3 execution modes (pure, hybrid, llvm)
- Basic CRUD operations
- Category filtering

**Missing in Unified:** SSpec parsing, utilities, 4th mode

---

## Migration Plan

### Phase 1: Extend Unified Library (6-10 hours)

**Test Database:**
1. Add schema for all tables (files, suites, tests, counters, timing, timing_runs, changes)
2. Add StringInterner integration
3. Port statistical analysis (percentiles, outlier detection, flaky detection)
4. Add test result tracking (update_test_result, get_or_create_*)
5. Add run management (cleanup_stale_runs, prune_runs, list_runs)
6. Add migration logic (merge dual-file → single-file)

**Feature Database:**
1. Add 4th mode (jit_status)
2. Port SSpec metadata parsing
3. Add utilities (sort, duplicate detection, orphan detection)

### Phase 2: Parallel Integration (2-3 hours)

- Add feature flag `USE_UNIFIED_DB`
- Run both implementations side-by-side
- Compare outputs for correctness

### Phase 3: Cutover (1 hour)

- Remove custom implementations
- Update all imports
- Run full test suite

### Phase 4: Cleanup (1 hour)

- Delete unused files
- Update documentation

---

## Files to Delete

```
src/app/test_runner_new/test_db_core.spl        # 556 lines
src/app/test_runner_new/test_db_io.spl          #  93 lines
src/app/test_runner_new/test_db_lock.spl        #  30 lines
src/app/test_runner_new/test_db_types.spl       # 190 lines (partial)
src/app/test_runner_new/test_runner_db.spl      # 119 lines
src/app/test_runner_new/feature_db.spl          # 423 lines
```

**Total:** 1,411 lines → **1,292 lines saved** (keeping enums)

---

## Key Decisions

### 1. Single-File vs Dual-File Storage

**Decision:** Use single file (`test_db.sdn`)

**Rationale:**
- Simpler implementation (one atomic operation)
- Unified library already uses this pattern
- Add migration to merge `test_db_runs.sdn` on first load

**Trade-off:** Slightly larger file, but simpler code

---

### 2. Method Compatibility

**Decision:** Match custom API exactly, then refactor later

**Rationale:**
- Minimize test runner changes
- Lower migration risk
- Can optimize API after migration

**Trade-off:** Some awkward API during transition

---

### 3. Statistical Analysis Location

**Decision:** Create new `src/lib/database/stats.spl`

**Rationale:**
- Shared by test and bug databases
- Clean separation of concerns
- Reusable for future databases

---

## Risk Mitigation

### Rollback Plan

**Git Tags:**
- `pre-db-migration` - Before migration
- `unified-lib-extended` - After Phase 1
- `parallel-integration` - After Phase 2
- `migration-complete` - After Phase 3

**Backups:**
```bash
cp doc/test/test_db.sdn doc/test/test_db.sdn.backup
cp doc/test/test_db_runs.sdn doc/test/test_db_runs.sdn.backup
cp doc/feature/feature_db.sdn doc/feature/feature_db.sdn.backup
```

### Data Safety

- Atomic writes prevent partial updates
- Backup on every save (`.bak` files)
- Validation after load (check row counts)
- Migration preserves all data

### Performance Monitoring

**Metrics:**
- Test suite runtime (±5% acceptable)
- Database save time (±10% acceptable)
- Memory usage (±20% acceptable)

---

## Success Criteria

### Functional
- ✅ All test runner features work
- ✅ Flaky test detection accurate
- ✅ Statistical analysis (percentiles) correct
- ✅ Run management works
- ✅ Documentation generation works
- ✅ Concurrent writes safe

### Non-Functional
- ✅ No performance regression
- ✅ No data loss
- ✅ All tests pass
- ✅ ~1,292 lines removed
- ✅ Single source of truth

---

## Next Steps

1. **Review plan** - Get approval for approach
2. **Execute Phase 1** - Extend unified library (6-10 hours)
3. **Test parallel** - Run both implementations (2-3 hours)
4. **Cutover** - Switch to unified only (1 hour)
5. **Cleanup** - Delete old code (1 hour)

**Total Time:** 10-15 hours development + 5-8 hours testing = **2-4 days**

---

## Questions to Resolve

1. **Single-file migration:** Approve merging `test_db_runs.sdn` into `test_db.sdn`?
2. **API compatibility:** Match custom API exactly, or clean up during migration?
3. **Testing scope:** Unit + integration tests sufficient, or need E2E suite?
4. **Timeline:** 2-4 day estimate acceptable, or need faster?

---

## Benefits Summary

### Short-Term
- Eliminate 1,292 lines of duplicate code
- Single implementation to maintain
- Consistent atomic operations

### Long-Term
- Easier to add new databases (build, lint, etc.)
- Better testing (shared infrastructure)
- Foundation for advanced features (query builder, indices, compression)

---

**Full Plan:** See `doc/plan/database_consolidation_plan.md`
