# Static lock-level ownership

Base: `release_phase3` at `f5c0f468556`; isolated branch
`work/static-lock-level-20261025`.

| Lane | Owner | Deliverable |
| --- | --- | --- |
| Architecture and guide | Astra guide agent | Exact annotation/checker contract, diagnostic policy, test plan, residuals |
| Implementation | Sol implementation agent | Parser metadata, shared checker, admission hooks, executable tests, current manual and evidence |
| Independent final review | Astra guide agent | Review exact final commit, call graph and cache correctness, negative cases and manual truth |
| Integration and merge | Root agent | Review results, verification status, exact target PR and landing |
| Lower-model sidecars | N/A | User requested the named guide/implementation pair; no additional sidecars |

Shared interfaces and scenario names are specified in
`doc/05_design/static_lock_level.md` and
`doc/03_plan/sys_test/static_lock_level.md`. No silent helper placeholders.

The guide owns architecture/design/test-plan/agent-task files; the implementation
agent owns source, specs, manual and implementation evidence. Neither agent
overwrites the other's files. Independent review must not accept partial scoped
effect enforcement as complete physical lock-order/lifetime enforcement.
