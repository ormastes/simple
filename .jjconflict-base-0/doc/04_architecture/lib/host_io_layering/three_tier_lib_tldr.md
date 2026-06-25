# Three-Tier Std-Lib — TL;DR

```sdn
tiers {
  core "src/lib/common — pure transforms; purity gate ratchets 14-file baseline"
  host "io_runtime + io/*_ops (sync) + host_io.{fileio,net,stdio} (async)"
  full "http/db/mcp_sdk/net_server — compose core + host; apps import here"
}
```

- Gate: `sh scripts/check/check-core-lib-purity.shs` — fails on NEW impure
  externs/imports in `common/`; baseline shrink-only.
- Host wrappers: 1 extern + 1 fn, no logic (no shelling out for primitives).
- Apps: facades only (`rg '\brt_'` per-dir gates in the MCP smoke check).
- No timeouts on blocking server reads; startup gates bound startup only.

Full doc: `three_tier_lib.md`. Plans: `doc/03_plan/lib/host_io_layering/`,
`doc/03_plan/app/mcp_framework/`.
