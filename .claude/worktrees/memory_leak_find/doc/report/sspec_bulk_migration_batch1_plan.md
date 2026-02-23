# SSpec Bulk Migration - Batch 1 Plan

**Date:** 2026-01-12
**Batch:** Smallest 10 files (pilot batch)
**Total Files:** 10 of 67 print-based files
**Strategy:** Start with smallest files to validate workflow

---

## Batch Selection Criteria

### Why Start with Smallest Files?

1. **Lower Risk:** Less code to review per file
2. **Faster Iteration:** Quick feedback on workflow
3. **Team Training:** Easier examples for team to learn from
4. **Pattern Discovery:** Find issues before larger files

### File Selection

**Sorted by Line Count (Smallest First):**

| # | File | Lines | Category | Est. Assertions |
|---|------|-------|----------|-----------------|
| 1 | `codegen/cranelift_spec.spl` | 143 | Codegen | ~8 |
| 2 | `ml/config_system_spec.spl` | 155 | ML | ~10 |
| 3 | `language/imports_spec.spl` | 159 | Language | ~12 |
| 4 | `concurrency/async_default_spec.spl` | 184 | Concurrency | ~15 |
| 5 | `types/enums_spec.spl` | 185 | Types | ~15 |
| 6 | `data_structures/dicts_spec.spl` | 192 | Data Structures | ~15 |
| 7 | `ml/training_engine_spec.spl` | 197 | ML | ~16 |
| 8 | `infrastructure/parser_spec.spl` | 199 | Infrastructure | ~16 |
| 9 | `data_structures/tuples_spec.spl` | 200 | Data Structures | ~16 |
| 10 | `language/closures_spec.spl` | 203 | Language | ~17 |
| **TOTAL** | **10 files** | **1,817** | **Mixed** | **~140** |

---

## Workflow Steps

### Phase A: Automated Migration (15 minutes)

**Step 1: Backup** (5 min)
```bash
# Create backup directory
mkdir -p migration_backups/batch1/$(date +%Y%m%d_%H%M%S)

# Copy original files
for f in cranelift_spec.spl config_system_spec.spl imports_spec.spl \
         async_default_spec.spl enums_spec.spl dicts_spec.spl \
         training_engine_spec.spl parser_spec.spl tuples_spec.spl \
         closures_spec.spl; do
    find simple/std_lib/test/features -name "$f" -exec cp {} migration_backups/batch1/$(date +%Y%m%d_%H%M%S)/ \;
done
```

**Step 2: Dry Run** (2 min)
```bash
# Preview changes
simple migrate --fix-sspec-docstrings --dry-run \
  simple/std_lib/test/features/codegen/cranelift_spec.spl \
  simple/std_lib/test/features/ml/config_system_spec.spl \
  simple/std_lib/test/features/language/imports_spec.spl \
  # ... (all 10 files)
```

**Step 3: Execute Migration** (3 min)
```bash
# Run automated migration
simple migrate --fix-sspec-docstrings \
  simple/std_lib/test/features/codegen/cranelift_spec.spl \
  simple/std_lib/test/features/ml/config_system_spec.spl \
  simple/std_lib/test/features/language/imports_spec.spl \
  simple/std_lib/test/features/concurrency/async_default_spec.spl \
  simple/std_lib/test/features/types/enums_spec.spl \
  simple/std_lib/test/features/data_structures/dicts_spec.spl \
  simple/std_lib/test/features/ml/training_engine_spec.spl \
  simple/std_lib/test/features/infrastructure/parser_spec.spl \
  simple/std_lib/test/features/data_structures/tuples_spec.spl \
  simple/std_lib/test/features/language/closures_spec.spl
```

**Step 4: Review Output** (5 min)
```bash
# Check for any errors or warnings
# Review summary statistics
# Spot-check 2-3 files for correctness
```

### Phase B: Manual Assertion Conversion (20-30 hours)

**Time Estimate:**
- 10 files × 14 assertions avg × 2 min/assertion = ~4.7 hours
- Range: 4-8 hours depending on complexity

**Distribution Strategy:**
- Developer 1: Files 1-4 (cranelift, config_system, imports, async_default)
- Developer 2: Files 5-7 (enums, dicts, training_engine)
- Developer 3: Files 8-10 (parser, tuples, closures)

**Process Per File:**
1. Open file in editor
2. Find all `if ... else:` blocks (empty)
3. Convert to `expect()` using guide
4. Commit after each file

**Expected Time Per Developer:** ~2-3 hours

### Phase C: Docstring Enhancement (20-30 hours)

**Time Estimate:**
- 10 files × 10 docstrings avg × 4 min/docstring = ~6.7 hours
- Range: 6-10 hours depending on detail level

**Distribution Strategy:**
- Each developer continues with same files
- Maintains context from assertion conversion

**Process Per File:**
1. Replace all `TODO: Add documentation here`
2. Add file-level comprehensive docstring
3. Add Given/When/Then for each `it` block
4. Add code examples where helpful
5. Cross-reference related features

**Expected Time Per Developer:** ~3 hours

### Phase D: Testing & Review (5-10 hours)

**Per File Testing:**
1. Run file to check syntax
2. Verify all tests pass
3. Review docstring quality
4. Run documentation generator (if available)

**Peer Review:**
- Each developer reviews another's files
- Check for consistency
- Verify completeness

**Expected Time:** 1-2 hours per developer

---

## Success Criteria

### Automated Migration

- [x] All 10 files migrated without errors
- [x] SSpec structure correctly generated
- [x] Manual tracking removed
- [x] Banner prints removed
- [x] Docstring placeholders added

### Manual Conversion

- [ ] All assertions converted to expect()
- [ ] No syntax errors
- [ ] All tests executable

### Documentation

- [ ] File-level docstrings complete
- [ ] All it blocks have Given/When/Then
- [ ] Code examples included
- [ ] Cross-references added

### Quality

- [ ] Peer review complete
- [ ] Tests passing
- [ ] Documentation generated successfully

---

## Risk Assessment

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Syntax errors from migration | LOW | MEDIUM | Already tested and validated |
| Assertion conversion mistakes | MEDIUM | LOW | Peer review catches issues |
| Inconsistent documentation | MEDIUM | LOW | Templates and examples provided |
| Time overruns | LOW | LOW | Conservative estimates |

---

## Rollback Plan

**If Issues Discovered:**

1. Stop migration immediately
2. Identify root cause
3. Restore from backup:
   ```bash
   cp migration_backups/batch1/TIMESTAMP/* destination/
   ```
4. Fix tool if needed
5. Re-run after validation

**Backup Location:** `migration_backups/batch1/TIMESTAMP/`

---

## Metrics to Track

### Automated Migration

- Time for migration: ______ seconds
- Files modified: ______ / 10
- Errors encountered: ______

### Manual Work

**Per File:**
- Time for assertions: ______ minutes
- Time for docstrings: ______ minutes
- Issues found: ______

**Summary:**
- Total assertion time: ______ hours
- Total docstring time: ______ hours
- Average time per file: ______ minutes

---

## Expected Outcomes

### Quantitative

- **Input:** 10 files, 1,817 lines, ~140 assertions
- **Output:** 10 files, ~2,400 lines (+32%), ~140 expect() assertions
- **Documentation:** ~100 docstrings added
- **Time:** ~10-15 hours total (vs ~40 hours manual)

### Qualitative

- Team learns workflow
- Process validated at small scale
- Issues discovered early
- Confidence for larger batches

---

## Next Steps After Batch 1

### If Successful (Expected)

1. Document lessons learned
2. Refine templates based on feedback
3. Plan Batch 2 (next 10 files, medium size)
4. Schedule team retrospective

### If Issues Found

1. Document problems
2. Adjust workflow
3. Re-run Batch 1 after fixes
4. Update documentation

---

## Team Communication

### Kickoff Message

**Subject:** SSpec Migration Batch 1 - Starting Today

Team,

We're beginning the first production batch of SSpec migration:
- **Files:** 10 smallest test files
- **Timeline:** This week
- **Your Role:** Assertion conversion + docstrings

**Your Assignment:**
- Developer 1: cranelift, config_system, imports, async_default
- Developer 2: enums, dicts, training_engine
- Developer 3: parser, tuples, closures

**Resources:**
- Assertion Guide: `doc/guide/sspec_assertion_conversion.md`
- Example: `pilot_conversion_example.spl`
- Questions: Ask in #sspec-migration channel

Let's ship great documentation! 🚀

### Daily Standup Questions

1. Which file(s) are you working on?
2. How far along? (assertions done? docstrings done?)
3. Any blockers or questions?
4. Anything that should be documented?

---

## Checklist

### Pre-Migration

- [ ] All team members have reviewed guides
- [ ] Backup strategy confirmed
- [ ] Time estimates communicated
- [ ] Assignment distributed

### During Migration

- [ ] Automated migration complete
- [ ] Spot-check passed
- [ ] Files distributed to developers

### Post-Conversion

- [ ] All assertions converted
- [ ] All docstrings filled
- [ ] Peer review complete
- [ ] Tests passing
- [ ] Metrics documented

### Wrap-Up

- [ ] Retrospective scheduled
- [ ] Lessons learned documented
- [ ] Next batch planned

---

**End of Batch 1 Plan**

**Status:** Ready to Execute
**Timeline:** This Week (5 days)
**Total Effort:** 10-15 hours (distributed)
**Risk:** LOW
