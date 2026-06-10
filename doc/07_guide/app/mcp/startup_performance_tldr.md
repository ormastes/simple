# MCP Startup Performance — TL;DR

Measured 2026-06-10: wrapper handshake 2722 ms = native server 1361 ms × 2
(wrapper probes with a full handshake, then execs the same binary again).

```sdn
startup_ladder {
  1 measure        "smoke + audit scripts; time direct vs wrapper"
  2 no_double_start "cache probe result by binary mtime+size"   # ~50% win
  3 run_artifacts  "exec native/SMF, never raw source in prod"
  4 lazy_init      "initialize needs no tool schemas; defer registry"
  5 iface_cache    "SHB mtime fast path: interfaces now, bodies on call"
  6 thin_layering  "core / thin-host / full keeps eager graph small"
  7 bg_compile     "dynSMF: interpret now, compile for next run"
  8 keep_warm      "daemon mode — last resort"
}
```

- Remove work before moving work: 2/4/5/6 beat 7/8.
- Wrapper duplication negates server-side wins — always re-measure through
  the wrapper.
- Startup gates bound startup, never idle: no read timeouts on MCP stdio.

Wave-1 wins (2026-06-10): json `find_text` → native `index_of` (85×, 2 KB);
import narrowing 61→49 modules, 130→72 ms load; handshake ~0.52 s (was ~0.55 s).
Diagnosis: `bin/simple deps normal <entry>` — see `deps_tool.md`.

Full guide: `startup_performance.md`. Layering plan:
`doc/03_plan/lib/host_io_layering/plan.md`.
