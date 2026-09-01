# Formal Verification Section Test Failures (106/274)

**UPDATE 2026-07-20:** This doc's core premise ("the specification modules
themselves do not exist in the codebase") is now false — re-triaged on
2026-07-20 against the same section and the `verification.*` modules are
present and substantially implemented (real classes/enums/functions, not
stubs). Only 11 of the original 16 specs still fail, with much smaller
per-spec failure counts, and the actual causes are narrow, specific defects
(a wildcard-symbol propagation bug, a missing `use` in a package `__init__`,
an alias-scoping bug, a member-resolution gap, a missing theorem, plus
several stale test-side `.?`/Option-unwrap misuses) — not "feature doesn't
exist." See the individual 2026-07-20-dated bug docs in this directory
(`verification_cache_invalidate_dependents_wildcard_symbol_`,
`verification_lean_init_missing_use_before_export_`,
`interp_use_as_alias_not_visible_in_function_body_`,
`contract_expr_forall_ge_call_member_not_found_`,
`lean_regen_memory_capabilities_missing_conversion_theorem_`) for current,
specific findings. Section is no longer purely "aspirational" — treat future
failures here as regular bugs, not as an accepted future-feature gap.

**Date:** 2026-07-18  
**Impact:** 106 test failures (all in 00_formal_verification section)  
**Pass Rate:** 168/274 (61.3%)  
**Classification:** FEATURE NOT IMPLEMENTED (aspirational spec section)

## Root Cause

The 00_formal_verification test section contains 16 spec files that document and test a formal verification system (Lean code generation, proof verification, verification caching, contract verification, etc.). **The specification modules themselves do not exist in the codebase.**

All 106 failures stem from missing implementations of:
- `verification.cache.{VerificationCache, CacheEntry, CacheStats}`
- `verification.lean.{LeanCodegenOptions, LeanCodegen, LeanTheorem, LeanBlock}`
- `verification.proof_unit.{ProofUnit}`
- `verification.fingerprint.{Fingerprint, simple_hash, ...}`
- `verification.state.{VerificationState}`
- And related supporting modules

## Failure Buckets (106 failures)

| Bucket | Error Signature | Specs Affected | Count | Type |
|--------|-----------------|---|-------|------|
| B1 | Missing functions/imports (unit, process, StringType, LEAN_RESERVED, print_summary) | 6 specs | 39 | Module not found |
| B2 | Unknown class/enum (LeanCodegenOptions, ProofRefResult, ContractExprKind) | 3 specs | 32 | Class definition missing |
| B3 | Dict method dispatch (with_module_name, ffi_in_verified_error, report_ffi_error) | 4 specs | 28 | Missing class wrappers for dict-created objects |
| B4 | Syntax/argument mismatches (shell constructor, function vs fn) | 2 specs | 10 | Spec-side issues |
| B5 | Unsupported construct errors (IO_FUNCTIONS, method name collisions) | 1 spec | 16 | Module structure issue |

**Note:** Buckets B1–B3 (99 failures) are all caused by missing verification.* module implementations.

## Affected Specs (16 files)

1. cache_correctness_spec.spl (10 failed) — missing verification.cache module
2. deterministic_emission_spec.spl (6 failed) — missing LeanCodegenOptions class
3. lean_basic_spec.spl (2 failed) — missing LEAN_RESERVED, print_summary
4. lean_block_integration_spec.spl (10 failed) — missing LeanCodegenOptions.with_module_name
5. lean_codegen_spec.spl (5 failed) — missing LeanCodegenOptions method dispatch
6. lean_workflow_spec.spl (7 failed) — missing StringType, shell constructor issue
7. memory_capabilities_spec.spl (2 failed) — missing print_summary function
8. naming_spec.spl (4 failed) — missing LEAN_RESERVED variable
9. proof_reference_spec.spl (16 failed) — missing ProofRefResult static methods
10. regeneration_spec.spl (6 failed) — missing StringType, LeanCodegenOptions.with_module_name
11. report_rendering_spec.spl (1 failed) — missing print_summary function
12. tool_checker_spec.spl (1 failed) — missing regen variable
13. toolchain_detection_spec.spl (8 failed) — missing process variable
14. unified_attrs_spec.spl (10 failed) — missing ContractExprKind.Forall variant
15. unsupported_construct_spec.spl (16 failed) — missing IO_FUNCTIONS, method issues
16. verification_diagnostics_spec.spl (2 failed) — missing ffi_in_verified_error method

## Classification

**Type:** ASPIRATIONAL SPEC SECTION — specs are correctly written and well-documented, but the implementation doesn't exist yet.

**Action:** These specs should remain in the test suite as documentation of the formal verification system's design. They are appropriate xfail candidates until the feature is implemented, OR the section should be marked as "future" in the test discovery if the runner supports such classification.

## Recommendations

1. **Do not skip tests** — the specs are valuable documentation of intended functionality.
2. **Mark section as xfail-expected** — if the test runner supports section-level xfail declarations, use that to prevent false alarms in CI.
3. **Implement verification modules** — when formal verification support is prioritized, these specs will guide the implementation.
4. **Minor spec fixes (optional, 10 failures):**
   - B4: tool_checker_spec syntax (function → fn) can be fixed immediately
   - B4: lean_workflow_spec shell constructor argument count can be verified against actual shell class signature

## Per-Spec Quick Fixes (if pursuing)

| Spec | Issue | Fix |
|------|-------|-----|
| tool_checker_spec.spl | "Replace 'function' with 'fn'" | Syntax error — change `function` to `fn` keyword |
| lean_workflow_spec.spl | "too many arguments for shell constructor" | Verify shell() class signature and adjust call sites |

---

**Status:** DOCUMENTED  
**No immediate action required** — this is a known future feature section.
