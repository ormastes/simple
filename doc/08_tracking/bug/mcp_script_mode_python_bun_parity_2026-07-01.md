# MCP script-mode Python/Bun parity gap

Date: 2026-07-01

## Status

Open.

## Symptom

`bin/simple_mcp_server` and `bin/simple_lsp_mcp_server` can run through the
checked-in script wrappers, but source/script startup is not yet at Python/Bun
cold-stdio parity.

Current local diagnostic:

```text
sh scripts/check/check-mcp-script-mode-perf.shs
mcp_script_perf_runs=5
python3_mcp_median_ms=26
bun_mcp_median_ms=34
simple_mcp_script_median_ms=365
simple_lsp_mcp_script_median_ms=60
mcp_script_perf_status=fail
```

## Constraints

- Do not default to native MCP only for speed while native `tools/call` returns
  `Missing tool name`.
- Do not add keep-warm daemon lifecycle just to hide cold-start cost.
- Keep the wrapper boundary: Codex, Claude, and Gemini launch the same repo MCP
  scripts.

## Likely root cause

The remaining gap is cold Simple source/interpreter startup and MCP app import
work, not stdio framing size. The LSP MCP path is closer but still slower than
the Python/Bun comparator on this host.

The architecture-preserving fast path is checked SMF execution. The first SMF
relocation blockers (`rt_dir_exists`, raw stdio, `text.from_char_code`) are
fixed in source, and bootstrap SMF initialize/tools-list now runs without
stderr. Deployed `bin/simple` cannot yet be refreshed because Stage 4
native-build fails with `cannot parse '0.0' as i64`; see
`doc/08_tracking/bug/mcp_smf_script_artifact_missing_rt_dir_exists_2026-07-01.md`.

2026-07-01 follow-up: bootstrap SMF initialize/tools-list now runs cleanly.
The source of the remaining gap was eager full-dispatch startup. The SMF path
now uses a core dispatcher for the core advertised tool set and keeps heavy
tool families out of startup.

```text
MCP_SCRIPT_PERF_STRICT=1 sh scripts/check/check-mcp-script-mode-perf.shs
python3_mcp_median_ms=35
bun_mcp_median_ms=40
simple_mcp_script_median_ms=29
simple_lsp_mcp_script_median_ms=30
mcp_script_perf_status=pass
```

The wrappers prefer checked SMF artifacts when present and fall back to source
mode when `SIMPLE_MCP_DISABLE_SMF=1` / `SIMPLE_LSP_MCP_DISABLE_SMF=1` is set.
The source MCP entrypoint keeps full dispatch for fallback; the checked MCP SMF
artifact currently carries the core-dispatch fast path.

## Verification target

`MCP_SCRIPT_PERF_STRICT=1 sh scripts/check/check-mcp-script-mode-perf.shs`
must pass on a normal developer host with `python3` and `bun` installed.

After the SMF relocation blocker is fixed, also run:

```bash
MCP_SCRIPT_PERF_USE_SMF=1 MCP_SCRIPT_PERF_STRICT=1 sh scripts/check/check-mcp-script-mode-perf.shs
```
