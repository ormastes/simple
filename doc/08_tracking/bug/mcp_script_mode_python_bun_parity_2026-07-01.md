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

The architecture-preserving fast path is checked SMF execution, but MCP SMF
artifacts currently fail relocation on `rt_dir_exists`; see
`doc/08_tracking/bug/mcp_smf_script_artifact_missing_rt_dir_exists_2026-07-01.md`.

## Verification target

`MCP_SCRIPT_PERF_STRICT=1 sh scripts/check/check-mcp-script-mode-perf.shs`
must pass on a normal developer host with `python3` and `bun` installed.

After the SMF relocation blocker is fixed, also run:

```bash
MCP_SCRIPT_PERF_USE_SMF=1 MCP_SCRIPT_PERF_STRICT=1 sh scripts/check/check-mcp-script-mode-perf.shs
```
