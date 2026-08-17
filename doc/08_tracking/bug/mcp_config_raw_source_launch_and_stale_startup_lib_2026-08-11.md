# MCP/LSP server family: raw-source client configs, stale startup-lib extraction, missing POSIX wrappers

**Date:** 2026-08-11
Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

## 1. FIXED — shipped MCP configs launched raw `.spl` source

`.claude/rules/code-style.md`: *"Production wrappers should execute cached
compiled artifacts, not raw source."* The two POSIX wrappers
(`bin/simple_mcp_server`, `bin/simple_lsp_mcp_server`) already comply and are
enforced by `scripts/check/check-mcp-wrapper-contract.shs`. **Nothing checked
the client CONFIGS**, and four of them bypassed the wrappers entirely:

| config | was | now |
|---|---|---|
| `.mcp.json` → `simple-lsp-mcp` | `node bin/mcp_stdio_bridge.js -- bin/simple run src/app/simple_lsp_mcp/main.spl` | `bin/simple_lsp_mcp_server` |
| `tools/claude-plugin/simple-mcp/.mcp.json` | `bin/simple src/app/mcp/main.spl` | `bin/simple_mcp_server` |
| `tools/claude-plugin/marketplace/plugins/simple-mcp/.mcp.json` | same | `bin/simple_mcp_server` |
| `tools/claude-plugin/simple-codex/.mcp.json` → `simple-mcp` | same | `bin/simple_mcp_server` |

The `.mcp.json` `_info` string justified the bypass with *"the cached native
server currently fails tools/call argument extraction"*. **That is stale.**
Measured 2026-08-11: `bin/release/x86_64-unknown-linux-gnu/simple_lsp_mcp_server`
answers `tools/call` `lsp_symbols` with a full `result.content` payload
(33,864 bytes), no `isError`, no `Missing tool name`.

### Measured before/after (median of 5 runs, `/usr/bin/time`, warm)

| lane | startup (`initialize`) | `lsp_symbols` call | max RSS |
|---|---|---|---|
| `simple-lsp-mcp` BEFORE (node bridge + raw source) | **0.20 s** | **4.15 s** | 82.9 MB idle / 87.4 MB |
| `simple-lsp-mcp` AFTER (`bin/simple_lsp_mcp_server`) | **0.03 s** | **3.68 s** | **4.1 MB** idle / 88.1 MB |
| `simple-mcp` BEFORE (`bin/simple src/app/mcp/main.spl`) | **0.50 s** | — | **171.6 MB** |
| `simple-mcp` AFTER (`bin/simple_mcp_server`) | **0.02 s** | — | **4.1 MB** |

→ 6.7×/25× faster startup, 20×/42× lower idle RSS, 11% faster hot request, and
the node stdio-bridge dependency is gone from the LSP lane.

### `SIMPLE_EXECUTION_MODE=interpreter` is load-bearing — do not "clean it up"

`run_lsp_symbols` spawns a child (`bin/simple src/app/cli/query_visibility.spl`)
that dominates call latency (3.5–3.9 s standalone). The env is **inherited by
that child**. Measured on the native server:

- with `SIMPLE_EXECUTION_MODE=interpreter`: call **4.86 s**, child 3.89 s
- without it: call **7.96 s**, child 3.53 s but server total +3.1 s

The first measurement of "native is 2× slower on tools/call" was this env
artifact, not a native regression. Related open perf item: the JIT/native child
lane is slower than the interpreter for `query_visibility` — worth a separate
investigation.

### Regression guard (with sabotage oracle)

`scripts/check/check-mcp-wrapper-contract.shs` now also asserts
`mcp_config_cached_artifact_contract`: none of the four configs may name a
`.spl` path outside a `"_"`-prefixed prose key. Verified non-vacuous — restoring
the raw-source launch in `.mcp.json` makes the guard print
`raw-source MCP launch in .mcp.json` and exit 1; reverting returns exit 0.

## 2. RECORDED — `config/mcp/mcp_startup_lib.shs` (388 lines) is OBSOLETE, not merely unwired

Referenced by **zero** launchers (only its own usage comment and docs). The
brief called for wiring it. **Do not wire it as written.** It is built around
the *source-compile* model the wrappers deliberately abandoned:
`mcp_compile_cached` + `.smf` cache + runtime resolution. It has **zero**
occurrences of `native_hash_is_valid`, probe stamps, or a `tools/call` probe —
the three things the current contract requires. Sourcing it would revert the
wrappers to source mode and trip the existing ban at
`check-mcp-wrapper-contract.shs:62-65` (`smf_runtime=`, `mode=source`).

**Action:** delete it, or rewrite it against the native hash-admission contract
and re-extract from the two working wrappers. Either is a real change to
untested surface and needs a spec first (see §5). Not done here.

## 3. RECORDED — JSON-RPC/stdio framing implemented 6× behind a shared module nobody imports

Sites: `src/app/mcp/main.spl`, `src/app/simple_lsp_mcp/json_helpers.spl` (367
lines), `src/app/t32_lsp_mcp/protocol.spl` (174 lines),
`examples/10_tooling/trace32_tools/t32_lsp_mcp/main.spl`, and the orphan below.
Deduping REROUTES callers rather than removing code, and two of the three live
sites are untested (§5) — spec first. Not done here.

## 4. RECORDED — `src/app/lsp_mcp/main.spl` (387 lines) is a true orphan

Scoped `/usr/bin/grep` over `src/app src/lib bin scripts config tools .mcp.json
test` finds exactly one reference: a line in
`scripts/check/ui_backend_isolation_baseline.txt`. Nothing builds, launches, or
imports it. Candidate for deletion once §3 decides which framing survives.

## 5. RESOLVED/RECORDED — missing binaries: obsidian is a STALE REFERENCE, t32 is a MISSING ARTIFACT

The brief flagged `bin/obsidian_lsp_mcp_server`. The real picture is broader —
`scripts/check/mcp_cmdline_probe_debug.spl` probes five servers and **three of
the five binaries do not exist**:

- **`bin/obsidian_lsp_mcp_server` — STALE REFERENCE.** No binary, no git
  history, no `src/app/obsidian*`, no `examples/obsidian-search/`. Per the MCP
  table in `.claude/rules/code-style.md` this server is *a separate package on
  its own version track*. **Fixed:** the dead
  `tools/claude-plugin/obsidian-search/.mcp.json` (which pointed at a
  repo-relative path that could never resolve, so every launch failed) is
  removed and the README now states the truth. The guard blocks its return.
- **`bin/t32_mcp_server`, `bin/t32_lsp_mcp_server` — MISSING ARTIFACT.** Source
  exists (`src/app/mcp_t32/`, `src/app/t32_lsp_mcp/`) and Windows `.cmd`
  wrappers exist, but there is no POSIX wrapper and no native under
  `bin/release/<triple>/`. Building them requires a native-build plus the same
  hash-admission/probe treatment; untested surface, spec first. Not done here.

## 6. Coverage gap (why §2–§4 were not merged)

`src/app/lsp_mcp/`, `src/app/t32_lsp_mcp/`, and `config/mcp/mcp_startup_lib.shs`
have no tests. Repo rule: merge only where covered, else write a modern SSpec
spec first or skip with a recorded reason. This document is that recorded
reason. The one change that *was* merged (§1) landed with an extension to an
existing, executable, sabotage-verified guard.

## 7. Not changed on purpose: `bin/simple_lsp_mcp_server.cmd`

The Windows wrapper defaults to raw source and requires
`SIMPLE_LSP_MCP_PREFER_NATIVE=1` to opt into the native. Its stale reason
comment ("native fails every tools/call") is disproven **on Linux**. Flipping a
Windows default that cannot be measured from this host is exactly the fail-open
the rules forbid, so the default is left opt-in. Re-measure on Windows and flip
there.

## 8. Pre-existing test-tree divergence recorded at landing (delta-PASS step-over)

`check-test-tree-divergence-delta.shs` verdict for this range:

```
base verdict: check-test-tree-divergence: FAIL — 857 diverged vs 856 baselined
  (1 new, 0 fixed-but-still-baselined); 5 mirror-only (3 unallowlisted,
  0 stale-allowlist); half-landed: skipped (no --base)
PASS — 4 pre-existing offender(s), 0 introduced by this range
```

This range introduces **zero** new divergence (it touches no file under
`test/`). The red is pre-existing, left by another session. Per the
scoped-delta escape rule the offender list must be recorded before landing:
the full 857-entry diverged list is committed alongside this record as
`doc/08_tracking/bug/test_tree_divergence_preexisting_2026-08-11.txt`
(sha256 `e4cd09c31d89971884242ed96f66108adf88e8f3ac5a284b3e823512c52e44c2`).

The other four guards all returned real, non-vacuous PASSes on
`094f7667f7ad..3345567480df`: conflict-tree 1 commit / 0 conflict trees;
conflict-markers 7 files / 0 markers; tree-size 1 commit / 112,817 files /
0 structural faults; no-revert 8 files / 0 reverts.

## Content re-verification 2026-08-17 (app-rest lane) — config half CONFIRMED FIXED

Classified by CONTENT only. `.mcp.json:30` now launches the compiled binary
(`exec "$PWD/bin/simple_lsp_mcp_server"`); no `mcp_stdio_bridge.js` and no raw
`.spl` launch remains for the simple lanes. (The JS bridge still on line 42 is
the unrelated `codex_stitch` server, not an MCP-family regression.) This matches
the doc's own "raw-source configs FIXED + guarded" status.
The remaining items — stale startup-lib extraction and the missing POSIX
wrappers — are explicitly RECORDED-not-fixed by this doc and stay OPEN; nothing
in `src/app/simple_lsp_mcp/main.spl` implements them. **No patch available in
`src/app/`; this is a backlog record, not a live app-code defect.**

## Re-verification 2026-08-17 (app-rest lane) — section 1 FIXED, sections 2-4 LIVE

FIXED: `.mcp.json:7-8,18-19,29-30` all `exec "$PWD/bin/simple_mcp_server"` /
`bin/simple_lsp_mcp_server` — no raw `.spl` launch remains, and the node bridge
is gone from the LSP lane.

STILL LIVE by content: `config/mcp/mcp_startup_lib.shs` (14,686 B) is still
present and obsolete, and the orphan `src/app/lsp_mcp/main.spl` (13,877 B)
still exists with its own dispatch (`:418` `make_error(id, -32601, ...)`).
