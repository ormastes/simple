# Pre-existing test-tree divergence record — enterprise-suite landing 2026-08-14

Required record for the test-tree-divergence scoped-delta escape (vcs.md):
landing range `425fdcc69c76..<enterprise-suite tip>` passed
`check-test-tree-divergence-delta` with:

```
PASS — 16 pre-existing offender(s), 0 introduced by this range
base verdict: FAIL — 828 diverged vs 814 baselined (15 new, 1 fixed-but-still-baselined);
2 mirror-only (0 unallowlisted, 0 stale-allowlist)
```

The 15-new/1-fixed offenders relative to the baseline pre-exist this range
(present at base 425fdcc69c76, left by other sessions). The full 828-line
diverged-offender list at base is retained by the guard at its stated temp
path during the run; representative head (all `integration:` pairs):

- integration:app/app_mcp_intensive_spec.spl
- integration:app/check_log_modes_spec.spl
- integration:app/cli_log_modes_spec.spl
- integration:app/feature_gen_log_modes_spec.spl
- integration:app/itf_log_modes_spec.spl
- integration:app/linkers_log_modes_spec.spl
- integration:app/llm_dashboard_log_modes_spec.spl
- integration:app/mcp_stdio_integration_spec.spl
- integration:app/optimize/optimize_cli_spec.spl
- integration:app/os_log_modes_spec.spl
- integration:app/primitive_api_lint_spec.spl
- integration:app/simple_lsp_mcp_stdio_spec.spl
- integration:app/simple_portal/simple_portal_content_db_spec.spl
- integration:app/simple_portal/simple_portal_server_spec.spl
- integration:app/spec_coverage_log_modes_spec.spl
- integration:app/spipe_quality_lint_spec.spl

This range adds specs only under `test/01_unit/` and `test/03_system/` with
no mirrored counterparts, introducing zero divergence. Baseline refresh for
the pre-existing offenders belongs to the session that landed them, per the
guard's no-silent-step-over rule.
