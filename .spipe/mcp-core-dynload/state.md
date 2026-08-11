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

## 2026-06-13 — implement + verify (wire)

- A/B/C/D all landed committed; specs 27+16+14 green (interpreter).
- Wire verification caught 2 NEW language bugs (doc/08_tracking/bug/native_module_var_bool_garbage_init_2026-06-13.md):
  1. native module-level `var = false` garbage-truthy (i64 `= 0` fine)
  2. fn that reads AND assigns same module var sees nil on read (BOTH modes) — getter-mediated read workaround
- After fixes + rebuild (854 KB): auto = core(20) first handshake 0.070s + one framed list_changed + full(151) on refetch; all = 151 no notif; core = 20 strict no notif; cap listChanged:true auto-only. Probe + wrapper OK (tool_set=auto).
- Phase: review (opus, in flight) → push
