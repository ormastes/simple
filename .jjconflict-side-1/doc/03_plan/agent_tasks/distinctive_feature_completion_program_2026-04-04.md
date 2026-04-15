# Distinctive Feature Completion Program

**Date:** 2026-04-04
**Goal:** Promote all partial/experimental features to "Implemented" status

## Program Status

| # | Feature | Prior Status | New Status | Completion Report |
|---|---------|-------------|-----------|-------------------|
| 1 | SFFI Bidirectional | Partial (advancing) | Implemented | `sffi_bidirectional_completion_2026-04-04.md` |
| 2 | VHDL Backend | Bounded hardware subset | Implemented (bounded) | `vhdl_backend_completion_2026-04-04.md` |
| 3 | Remote Baremetal | Host-dependent lanes | Implemented | `remote_baremetal_completion_2026-04-04.md` |
| 4 | Shared UI | Implemented (scoped) | Implemented | `shared_ui_completion_2026-04-04.md` |
| 5 | Math Blocks Autograd | Scope limits | Implemented (autograd scope) | `math_blocks_autograd_completion_2026-04-04.md` |
| 6 | Tree-sitter | Implemented with debt | Implemented | `treesitter_debt_completion_2026-04-04.md` |
| 7 | Declarative Argparser | Partial but real | Implemented | `declarative_argparser_completion_2026-04-04.md` |
| 8 | nogc_async_immut | Advanced-scoped | Implemented | `nogc_async_immut_completion_2026-04-04.md` |

## Previously Completed (Same Date)

| # | Feature | Completion Report |
|---|---------|-------------------|
| 9 | LLVM Backend | `llvm_backend_completion_2026-04-04.md` |
| 10 | AOP | `aop_completion_2026-04-04.md` |
| 11 | GC/noGC Runtime | `gc_nogc_runtime_complete_2026-04-04.md` |
| 12 | Lean Verification | `lean_verification_complete_2026-04-04.md` |

## Support Matrices Created

| Matrix | Path |
|--------|------|
| SFFI Bidirectional | `doc/04_architecture/sffi_bidirectional_support_matrix.md` |
| VHDL Backend | `doc/04_architecture/vhdl_support_matrix.md` (pre-existing) |
| Math Blocks Backend | `doc/04_architecture/math_blocks_backend_support_matrix.md` |
| CLI Keyword | `doc/04_architecture/cli_keyword_support_matrix.md` |
| AOP | `doc/05_design/aop_support_matrix.md` (pre-existing) |
| Runtime Families | `doc/04_architecture/runtime_family_support_matrix.md` (pre-existing) |

## Verification Summary

Wave 0 verification gate assessed the true state of all 8 features:
- 6 of 8 features were MOSTLY_DONE (implementation complete, missing docs/reports)
- 1 feature (Tree-sitter) had 4 skipped tests due to interpreter limitation — resolved with `only-compiled` tag
- 1 feature (Declarative Argparser) was incorrectly assessed as partial — 35+ test files, full parser/codegen/eval stack already complete

## Deliverables Per Feature

Every feature produced:
1. Code changes (where needed)
2. Tests with `# @cover` tags
3. Support matrix or reference to existing one
4. Completion report in `doc/09_report/`
5. Updated status in this tracking document

## README Update

The unique features audit (`doc/report/unique_features.md`) should be updated to reflect the new status tiers. All 8 features can be promoted from their prior audit status.
