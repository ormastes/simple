# native-build lane crashes at startup: "field access on nil receiver" (SIGILL, zero output)

- **Date:** 2026-07-25 (evening)
- **Lane:** deployed stage4 `bin/simple native-build`, macOS
- **Status:** open — bisect/fix in progress; broke SimpleOS harness runs 3-4 and MCP artifact rebuilds

## Symptom
`bin/simple native-build --entry <any .spl> --output <bin>` exits 132 (SIGILL) printing
`runtime error: field access on nil receiver` before ANY compile output — even for a
3-line hello probe. The harness's `native-build.out` files are 0 bytes.

## Regression window
- WORKED: 03:45 deploy (main `4ed680f5`-era) — SimpleOS harness run 2 produced real
  parser diagnostics through this lane.
- BROKEN: every build from `d5a6312d` onward, including origin tip `3a6982e8`.
- Window contents: today's CLI refactors (`6aec1b71` native-build parent lightweight,
  `4392ce6d` global flag split, `debc189e` seed-delegate fallback, `6cf217f0` exe via
  /proc/$PPID, `0531ca8c` exe identity in-process). `/proc` does not exist on macOS —
  prime suspect class: nil exe-path Option flowing into a field access.

## Masked consequences (already burned today)
- SimpleOS WM harness runs 3-4 reported `wm-simple-web-build-timeout` (900s/2700s) with
  EMPTY build logs — the "timeout" was this crash/hang, not slowness. Run 3's
  "0 parser errors" was vacuous.
- MCP `node_repl` artifact rebuild died silently twice (agent lane), then reproduced
  attended: same nil-receiver crash.

## Gate gap (fix alongside)
The redeploy gate (`scripts/check/cert/redeploy_gate/`) runs NO native-build fixture, so
a binary with a dead native-build lane gates 10-11/11 and deploys cleanly — this shipped
twice today. Add a minimal `native-build --entry hello --output tmp && run it` check.
