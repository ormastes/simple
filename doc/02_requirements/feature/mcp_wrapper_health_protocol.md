# MCP Wrapper Health & Self-Recovery Protocol

**Type:** Feature
**Category:** Infrastructure / MCP / Reliability
**Priority:** High
**Proposed:** 2026-04-16
**Status:** Partially Implemented (sentinel cache live in `mcp_startup_lib.sh`)

## Problem

The MCP wrapper scripts (`bin/simple_mcp_server`, `bin/simple_lsp_mcp_server`, `bin/serial_mcp_server`, `bin/t32_mcp_server`, `bin/t32_lsp_mcp_server`, `bin/obsidian_lsp_mcp_server`) bootstrap a Simple-language MCP server in three modes:

1. **Interpret mode:** `bin/simple <main.spl>` (~5 s startup, always works)
2. **Cached SMF mode:** `bin/simple <cached.smf>` (~200 ms startup, may fail)
3. **Native mode:** prebuilt ELF binary (~50 ms startup, may segfault)

Today (2026-04-16), failures in mode 2 and mode 3 produce **silent corruption**:
- A `.smf` with unresolved relocations exits rc=1 with no useful stderr (only the `.simple/logs/<server>_stderr.log` shows it, which Claude Code's `/mcp` doesn't surface).
- A segfaulting native binary exits rc=139 and Claude Code reports "Failed to reconnect to <server>" with no diagnostic.
- The wrapper has no notion of "this artifact was healthy 1 hour ago and now isn't" — it re-tries the broken artifact every reconnect.

Concrete incidents this week:
- `simple_mcp_server` cached `.smf`: `Undefined symbol: _sdk_find_simple_binary (relocation 177)` on warm reload.
- `simple_lsp_mcp_server` cached `.smf`: `rt_interp_call: invalid function name encoding` infinite loop until timeout.
- `build/native/simple_mcp_native`: SIGSEGV on initialize.
- `build/native/simple_lsp_mcp_native`: SIGSEGV on initialize.
- `serial-mcp`: "Failed to reconnect" with no diagnostic surface.

The 2026-04-16 emergency fix added an opt-in cache mechanism (`SIMPLE_MCP_DISABLE_CACHE`) and a `.smf.ok` sentinel that requires a clean compile. This is a tactical patch; the strategic gap is a **standard health-check protocol** that:

1. Validates each artifact tier (native → cached → interpret) before exec.
2. Cascades down on validation failure.
3. Records the failure with provenance (see [file_change_provenance_query.md](file_change_provenance_query.md) for the broader pattern).
4. Surfaces actionable diagnostics to MCP clients.

## Proposed Solution

### 1. Standardize the wrapper contract

Every MCP wrapper sources `config/mcp/mcp_startup_lib.sh` and calls one entry point:
```sh
mcp_run "$ENTRY_SPL" "$NATIVE_BIN" "$LIB_PATH" "$@"
```

`mcp_run` walks the **artifact-tier ladder**:

| Tier | Probe | Promote on success | Fall back on failure |
|------|-------|--------------------|----------------------|
| `native` | `<bin> --health-check` exits 0 within 2 s | `<bin>.ok` sentinel | `cached` |
| `cached` | `<smf>.ok` exists AND `<runtime> <smf> --health-check` exits 0 within 3 s | (already promoted) | `interpret` |
| `interpret` | always | (none) | hard fail |

If the chosen tier later fails at runtime (process exits non-zero within 60 s of accepting the first JSON-RPC message), `mcp_run` records a "demotion event" so the next reconnect drops to the next tier and skips the broken one for `MCP_DEMOTION_TTL=600` seconds.

### 2. Universal `--health-check` mode

Every MCP server (Simple-source AND native) implements:
```
$ <server> --health-check
{"healthy":true,"server":"simple-mcp-full","version":"4.0.0","tools":102,"capabilities":["tools","resources","prompts","logging"]}
```
Returns rc=0 on success; rc=1 on any failure with a one-line stderr explanation. The native ELF binary's `--health-check` is the same entry point as the regular MCP loop but takes a single fake `initialize` request, validates it produces a well-formed response, and exits.

### 3. `simple mcp doctor` CLI

A diagnostic that runs all wrappers' `--health-check` and reports:
```
$ simple mcp doctor
simple-mcp:
  native:    ✗ FAIL  (rc=139, SIGSEGV)         demoted until 2026-04-16T10:00Z
  cached:    ✗ FAIL  (rc=1, Undefined symbol _sdk_find_simple_binary)
  interpret: ✓ OK    (5.2 s startup, 102 tools)
  → ACTIVE: interpret  (next reconnect)

simple-lsp-mcp:
  native:    ✗ FAIL  (rc=139, SIGSEGV)         demoted until 2026-04-16T10:00Z
  cached:    ✗ FAIL  (rc=124, rt_interp_call loop)  demoted until 2026-04-16T10:00Z
  interpret: ✓ OK    (3.1 s startup, 14 tools)
  → ACTIVE: interpret

serial-mcp:
  native:    (no native binary)
  cached:    ✓ OK    (180 ms startup, 5 tools)
  → ACTIVE: cached

Recommendations:
  - Rebuild native simple_mcp / simple_lsp_mcp binaries:
      simple build --native --target=mcp,lsp_mcp
  - Investigate AOT codegen: see doc/02_requirements/feature/file_change_provenance_query.md
    for tooling that traces what changed since the last working .smf.
```

### 4. MCP self-reporting

Each MCP server exposes a `system/health` notification on its own stream:
```json
{"jsonrpc":"2.0","method":"system/health","params":{"tier":"interpret","reason":"native_demoted","sticky_until":"2026-04-16T10:00Z"}}
```

Claude Code's `/mcp` UI can surface this so the user knows "MCP is up but on slow path; native binary needs rebuild."

### 5. Demotion ledger

`.simple/state/mcp_demotions.sdn`:
```sdn
demotions: [
  { server: "simple_mcp", tier: "native", since: "2026-04-15T10:56Z",
    reason: "SIGSEGV at startup, rc=139",
    binary_sha: "sha256:9f01...", expires: "2026-04-16T10:56Z" },
  { server: "simple_mcp", tier: "cached", since: "2026-04-16T08:46Z",
    reason: "Undefined symbol _sdk_find_simple_binary at relocation 177",
    smf_sha: "sha256:b3...", expires: "2026-04-16T09:46Z" },
]
```

`simple mcp doctor --clear-demotions` lets the user force re-probing after a fix.

## Implementation Notes

- **Already implemented (2026-04-16):**
  - `.smf.ok` sentinel in `config/mcp/mcp_startup_lib.sh`
  - `SIMPLE_MCP_DISABLE_CACHE` env opt-out
  - Compile-time warning detection blocks promotion
  - 3-second SMF probe before promotion
- **Remaining work:**
  - Native tier health-check + demotion
  - `simple mcp doctor` CLI
  - `--health-check` flag in MCP server source loops (5 wrappers × ~10 lines each)
  - Demotion ledger + 1-hour TTL logic
  - `system/health` notification in MCP protocol layer

## Acceptance Criteria

- [ ] `simple mcp doctor` lists all 6 wrappers with per-tier status.
- [ ] Forcing a broken native binary (e.g. `dd if=/dev/urandom of=build/native/simple_mcp_native bs=1 count=100`) causes the wrapper to demote and use cached/interpret on next reconnect, without hanging.
- [ ] Demotion is sticky for 1 hour by default; expires automatically.
- [ ] Claude Code `/mcp` reload after a demotion shows the wrapper still working (just on slow tier).
- [ ] `--clear-demotions` makes the wrapper re-probe immediately.

## Why Not Just Catch Errors at Reconnect?

Claude Code's MCP client doesn't currently surface stderr from the wrapper or distinguish "process exited non-zero" from "process never responded to initialize". Without the demotion ledger, every reconnect repeats the same failed exec.

## Related

- `file_change_provenance_query.md` — sibling DX feature; doctor's "what changed since last working" recommendation links here.
- `wip_topic_commit_bundling.md` — completes the post-fix triage workflow (doctor identifies → bundling commits the fix).
- `mcp_lsp_tools.md` — adjacent MCP tool surface improvements.
- `simple_cli_mcp_completeness.md` — `simple mcp doctor` is one of the gaps named there.

## Out of Scope

- Auto-rebuild on demotion (too expensive; user explicit).
- Cross-machine demotion sync.
- Health-check authentication (local stdio MCP only).
