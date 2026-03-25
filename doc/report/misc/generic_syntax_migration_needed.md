# Generic Syntax Migration Needed

**Date:** 2026-01-20
**Status:** Documentation migration required
**Scope:** 167 markdown files + documentation

---

## Summary

The codebase is migrating from deprecated `[]` generic syntax to the new `<>` syntax. While code files have been largely updated, **167 markdown documentation files** still contain examples using the old syntax.

---

## Completed (Session 2026-01-20)

### Code Files ✅
- [x] `src/driver/tests/interpreter_stdlib_syntax.rs` - 3 occurrences
- [x] `src/driver/tests/capability_tests.rs` - 1 occurrence
- [x] `src/driver/tests/interpreter_advanced_features_tests.rs` - 3 occurrences
- [x] `src/driver/tests/interpreter_generics_tests.rs` - 2 occurrences
- [x] `src/compiler/src/context_pack.rs` - 1 occurrence
- [x] `src/compiler/src/api_surface.rs` - 2 occurrences (formatter fix)

### Test Infrastructure ✅
- [x] Deprecation warning tests verified (31 tests passing)
- [x] Parser accepts both syntaxes (with warnings for old)

### Project Documentation ✅
- [x] `CLAUDE.md` - Already using new syntax correctly

---

## Remaining Work (167 files)

### High Priority Documentation (Session 2)

**Core Guides (need immediate update):**
1. `doc/guide/common_mistakes.md`
2. `doc/guide/coding_style.md`
3. `doc/guide/sspec_writing.md`
4. `doc/guide/sspec_complete_example.md`
5. `simple/bug_report.md`
6. `simple/improve_request.md`

**Specs (user-facing):**
7. `doc/spec/stdlib.md`
8. `doc/spec/sspec_manual.md`
9. `doc/spec/doctest_readme.md`

**Skills (LLM instructions):**
10. `.claude/skills/doc.md`
11. `.claude/skills/design.md`
12. `.claude/skills/architecture.md`
13. `.claude/skills/stdlib.md`

### Medium Priority (Session 3)

**Generated Specs (auto-generated from SSpec tests):**
- `doc/spec/generated/traits.md`
- `doc/spec/generated/functions.md`
- `doc/spec/generated/data_structures.md`
- `doc/spec/generated/memory.md`
- `doc/spec/generated/metaprogramming.md`
- `doc/spec/generated/concurrency.md`
- `doc/spec/generated/async_default.md`
- `doc/spec/generated/suspension_operator.md`

**Migration Documentation (keep both for education):**
- `doc/design/generic_syntax_deprecation_plan.md` - Keep both syntaxes
- `doc/design/GENERIC_SYNTAX_MIGRATION_SUMMARY.md` - Keep both syntaxes
- `doc/design/GENERIC_SYNTAX_MIGRATION_FAQ.md` - Keep both syntaxes
- `doc/design/type_parameter_syntax_analysis.md` - Keep both syntaxes

### Low Priority (Session 4+)

**Research Documents (144 files):**
- `doc/research/*.md` - Historical research, update as encountered
- `doc/report/*.md` - Session reports, update only recent ones
- `doc/plan/*.md` - Implementation plans, update active ones
- `doc/archive/*.md` - Leave as-is (historical)

---

## Migration Strategy

### Automated Migration
```bash
# Run the generic syntax migration tool on documentation
find doc -name "*.md" -not -path "doc/archive/*" \
  -not -path "doc/design/*generic*" \
  -exec simple migrate --fix-generics {} \;
```

### Manual Review Needed
- Migration documentation (keep both syntaxes for educational purposes)
- Archived documents (historical record)
- Generated documentation (regenerate from specs)

---

## Exceptions (Do NOT migrate)

1. **`src/parser/tests/deprecation_warnings.rs`** - Testing the warning system itself
2. **`doc/design/*GENERIC_SYNTAX_MIGRATION*.md`** - Educational documentation about the migration
3. **`doc/archive/**/*.md`** - Historical documents
4. **Files explicitly documenting the old syntax** - Keep for backwards compatibility docs

---

## Session Plan

### Session 2 (Next): High Priority (6 files, ~30 min)
- Core guides (6 files)
- Bug/improvement report templates (2 files)
- Key specs (3 files)
- LLM skills (4 files)

### Session 3: Medium Priority (20 files, ~45 min)
- Generated specs (regenerate from SSpec tests)
- Keep migration docs as-is

### Session 4: Automated Bulk Migration (144 files, ~60 min)
- Run migration tool on remaining files
- Manual review of results
- Test documentation builds

---

## Verification Checklist

After each session:
- [ ] Run `cargo test --workspace` - All tests pass
- [ ] Run `make check` - Formatting, linting pass
- [ ] Check documentation builds correctly
- [ ] Verify examples in docs compile/run

---

## Notes

- The migration tool (`simple migrate --fix-generics`) exists but needs refinement
- Parser accepts both syntaxes (old triggers deprecation warnings)
- Timeline: Deprecation warnings active, `[]` will be removed in v1.0.0
- All new code MUST use `<>` syntax
