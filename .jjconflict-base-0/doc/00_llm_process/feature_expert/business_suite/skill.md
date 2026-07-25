# Business Suite (Simple ERP) Feature Expert

## Role

Maintain feature-specific process knowledge for the ERP business-suite framework (guarded-write gate, lane registry, UBS kernel, web/report/dashboard surfaces). Use this skill when work touches `examples/12_business/simple_erp/` and keep it current as the pipeline produces new artifacts.

## Pipeline Links

- [research](../skill_command/skills/pipe/research/skill.md)
- [design](../skill_command/skills/pipe/design/skill.md)
- [impl](../skill_command/skills/pipe/impl/skill.md)
- [verify](../skill_command/skills/pipe/verify/skill.md)
- [release](../skill_command/skills/pipe/release/skill.md)

## Feature Links

- [Source (submodule)](../../../../examples/12_business/simple_erp/) — also standalone: https://github.com/ormastes/simple-erp
- [Framework gate](../../../../examples/12_business/simple_erp/src/framework/guarded.spl) / [lane registry](../../../../examples/12_business/simple_erp/src/framework/registry.spl) / [org-as-data](../../../../examples/12_business/simple_erp/src/framework/org.spl)
- [UBS kernel](../../../../examples/12_business/simple_erp/src/kernel/) — event log, projection, posting, durable log, snapshot, key index, commit queue
- [Lanes](../../../../examples/12_business/simple_erp/src/lanes/) — crm, reservation, sale, market, restaurant, clinic (extension proof)
- [Guide](../../../07_guide/app/simple_erp/business_framework.md)
- [Extension design](../../../05_design/simple_erp_extension.md)
- [Requirements REQ-001..043](../../../02_requirements/feature/simple_erp.md)
- [SAP/peer comparison](../../../01_research/domain/simple_erp_vs_sap.md)
- [Domain research](../../../01_research/domain/simple_erp.md) / [local research](../../../01_research/local/simple_erp.md)
- [System specs](../../../../test/03_system/app/simple_erp/feature/) — catalog, business_suite, dashboard, bigbiz
- [Unit specs](../../../../examples/12_business/simple_erp/ubs_test/) — 21 specs; verify with `✗`/`N failures` grep, never bare `PASS`

## Handoff Notes (2026-07-03)

- Gate contract: session → RBAC → validation → idempotency; closed reasons `accepted|invalid-session|forbidden|invalid-record|duplicate-key|needs-approval`. RBAC single source: `org_role_can` over `default_roles()`.
- New business = one `LaneDef` registration + one lane module (see `src/extension_demo.spl`, zero framework edits).
- Tracked next steps: lane auto-posting to the ledger, database-backed store, runner green-wash bug fix.

## Update Rule

After research, requirements, architecture, design, implementation, verification, or release work changes this feature area, add or refresh links here BEFORE committing, so the next agent starts from the current project state.

Template: [feature_skill.md](../../template/feature_skill.md)
