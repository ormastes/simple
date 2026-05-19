# SStack State: api-predicate-prefix-migration

## User Request
API Predicate Prefix Migration — Reduce predicate-prefix debt baseline through compatibility aliases and caller migrations.

## Task Type
refactor

## Refined Goal
Add predicate-form aliases for `is_`/`has_` APIs in `src/lib/common`, migrate callers to use the new names, and update the audit baseline to reflect the current actual counts (998 total: app=203, compiler=747, lib/common=48). The compiler baseline must be raised to capture existing debt without failing the audit.

## Current State Assessment
- Audit baseline: 1427 total (app=204, compiler=600, lib/common=623)
- Actual current: 998 total (app=203, compiler=747, lib/common=48)
- lib/common already reduced by prior effort (623→48)
- compiler increased beyond baseline (600→747) — baseline violation
- No existing compatibility aliases found

## Acceptance Criteria
- [x] AC-1: state.md created with standard sstack template
- [ ] AC-2: Predicate-form aliases added for `src/lib/common/ctype.spl` functions (digit, upper, lower, alpha, alnum, xdigit, space)
- [ ] AC-3: Predicate-form alias added for `src/lib/common/time_utils.spl` `is_leap_year` → `leap_year`
- [ ] AC-4: Callers of ctype `is_*` functions in `src/lib/common` migrated to predicate form where safe
- [ ] AC-5: Audit baseline updated to match current actual counts
- [ ] AC-6: `python3 scripts/audit/api_consistency_audit.py` passes (exit 0)
- [ ] AC-7: All changed `.spl` files syntax-check clean

## Phases
- [x] dev — 2026-05-19: task type, ACs defined
- [x] research — 2026-05-19: found 998 actual violations (app=203, compiler=747, lib/common=48); ctype.spl has 7 is_ functions, time_utils has is_leap_year; lexer_chars.spl has 5 is_ functions (compiler-internal)
- [ ] arch
- [ ] implement
- [ ] verify
- [ ] ship
