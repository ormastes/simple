# Stitch MCP: import crash `File is not defined` in Kimi-spawned environments; auth keys absent on this host

- **Filed:** 2026-09-15
- **Status:** OPEN
- **Severity:** medium — one optional MCP server red under Kimi Code (and any
  client that spawns it without the interactive Git Bash environment)
- **Host:** Windows 11, node v20.12.1 (`C:\dev\tool\nodejs\node.exe`), kimi 0.43.0

## Symptom

The `stitch` entry (`bash -lc 'if [ -f ~/.security/env.sh ]; then . ~/.security/env.sh; fi; exec npx -y @_davideast/stitch-mcp proxy'`) fails under Kimi Code with the child crashing at import time:

```
✖ Unexpected error: ReferenceError: File is not defined
    at file:///home/ormastes/.npm/_npx/829c6278c197c365/node_modules/@_davideast/stitch-mcp/dist/chunk-spbm03bj.js:12031:50
```

Two independent problems hide behind this one red entry:

1. **Environment-dependent crash.** The same command string run from an
   interactive Git Bash (or reproduced via `spawnSync('bash', ['-lc', …],
   {shell:false})` from node) does NOT hit `File is not defined` — it reaches
   `StitchProxy requires an API key (STITCH_API_KEY or access token
   (STITCH_ACCESS_TOKEN))`. The crashing child's npm cache path is
   `/home/ormastes/.npm/...`, i.e. the Kimi-spawned login shell resolves a
   different HOME (MSYS home, not `C:\Users\ormas`) and therefore a different
   npm/npx resolution path. `typeof File` is `'function'` on the interactive
   node v20.12.1, so the crash implies the spawned child resolved an older node
   and/or a stale cached stitch-mcp build from that other HOME. Not pinned down
   further; the cache root was not reachable from the investigating shell.
2. **No credentials on this host.** `~/.security/env.sh` does not exist, so
   even a healthy stitch-mcp cannot authenticate here. This part is expected
   and outside the repo's control.

## Impact

`stitch` reports `failed` under Kimi Code (and would under any client on this
machine) regardless of config spelling — the launch mechanism itself is fine
(`bash` is a real exe, spawnable with `shell:false`; the package runs).

## Workarounds

- Record `STITCH_API_KEY`/`STITCH_ACCESS_TOKEN` into `~/.security/env.sh`
  (mode 600) to clear problem 2.
- If problem 1 persists after that, pin the node executable inside the bash
  snippet (absolute path to a known-good node) instead of relying on whatever
  the spawned login shell resolves, and/or clear the stale
  `/home/ormastes/.npm/_npx` cache so `npx -y` re-resolves stitch-mcp.

## Notes

- The `_info` comment on the `stitch` entry in `.kimi-code/mcp.json` records
  the measured behavior; `doc/07_guide/infra/model_providers/kimi.md` (MCP on
  Kimi Code) summarizes it.
