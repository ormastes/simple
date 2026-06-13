# SPipe dev state — mcp-core-dynload

Feature: core tool-set as default + dynload upgrade via notifications/tools/list_changed; full set choosable.
Plan: doc/03_plan/app/mcp/mcp_core_default_dynload_plan_2026-06-13.md
Predecessor lane: .spipe/dep-analysis-handshake-perf (T1-T4, 2026-06-12)

## 2026-06-13 — wave start

- Phase: implement (research+spec folded into plan doc — contract table is the spec)
- Baseline re-measured: handshake all=1.504s, core=0.067s (build/bootstrap/mcp-package/simple_mcp_server)
- Tasks A(main.spl)/B(cache+perf spec)/C(specs)/D(guide) spawned parallel sonnet/haiku, disjoint scopes
- Then: E rebuild+measure (orchestrator), R opus review
- Open hazards: native env_get P1 (env-var selection dead in native); parallel sessions may touch main.spl
