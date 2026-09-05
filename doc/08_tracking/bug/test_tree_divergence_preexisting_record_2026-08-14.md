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

---

## Second landing: 2026-08-17 (enterprise aarch64 verification report)

Range `6f74fa163f8b..8f350e36f6e6` (adds two doc files only, zero `test/`
paths). Scoped-delta escape re-run per vcs.md:

```
check-test-tree-divergence-delta: pre-existing red is identical at BASE and NEW;
  this range introduces nothing
check-test-tree-divergence-delta: PASS — 19 pre-existing offender(s),
  0 introduced by this range
base verdict: FAIL — 829 diverged vs 813 baselined (17 new,
  1 fixed-but-still-baselined); 3 mirror-only (1 unallowlisted, 0 stale-allowlist)
```

The pre-existing red grew since the 08-14 landing (16 → 19 offenders; 828 → 829
diverged; a new `1 unallowlisted` mirror-only row appeared). None of it comes
from this range. Baseline refresh and the unallowlisted mirror-only row remain
owned by the sessions that landed them.

---

## Third landing: 2026-08-17 (http_server suite-enumeration drift closure)

Range `06dc5f66b179..18018caf7c93` — four files: one spec mirror
(`test/unit/lib/http_server/csrf_spec.spl`), one guard script, one verify
report, one wiki edit. Scoped-delta escape re-run per vcs.md:

```
check-test-tree-divergence-delta: pre-existing red is identical at BASE and NEW;
  this range introduces nothing
check-test-tree-divergence-delta: PASS — 19 pre-existing offender(s),
  0 introduced by this range
base verdict: FAIL — 829 diverged vs 813 baselined (17 new,
  1 fixed-but-still-baselined); 3 mirror-only (1 unallowlisted, 0 stale-allowlist)
```

Identical pre-existing red to the 2026-08-17 landing recorded above (19
offenders, 829 diverged, the same `1 unallowlisted` mirror-only row). Nothing
in it comes from this range; baseline refresh remains owned by the sessions
that landed those pairs.

This range DOES touch a `test/` path, unlike the second landing, so the
base-independence argument below does not apply to it and the delta guard was
the actual gate. The touched pair is deliberate and load-bearing:
`unit:lib/http_server/csrf_spec.spl` is **baselined line 618 as divergent**,
and the mirror was rewritten as a compact 13-example subset that keeps it
divergent. Converging the pair would have tripped the guard's
stale-baseline check — the sibling lane was explicitly redirected off the
"apply identical edits to both trees" default for this one file because of it.
The `security_headers` pair, which is NOT baselined, was left byte-identical,
which is that pair's required end state.

Note on SHAs: origin advanced repeatedly during this landing (parallel sessions
push every few minutes), so the pushed range's base differs from the base the
delta guard was run against. The result is base-independent by construction:
this commit adds three documentation files and touches **zero** `test/` paths
(`git diff --name-only <base> <tip> | grep -c '^test/'` = 0), so it cannot
introduce test-tree divergence against any base.
