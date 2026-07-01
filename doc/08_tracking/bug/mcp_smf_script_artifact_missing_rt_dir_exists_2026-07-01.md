# MCP SMF script artifact missing `rt_dir_exists`

Date: 2026-07-01

## Status

Open.

## Symptom

Compiling MCP script entrypoints to SMF succeeds, but running the MCP SMF
artifact fails before serving stdio:

```text
env SIMPLE_LIB=src bin/simple compile src/app/mcp/main.spl -o build/mcp-script/simple_mcp_server.smf
env SIMPLE_MCP_TOOL_SET=core SIMPLE_LIB=src bin/simple build/mcp-script/simple_mcp_server.smf

error: load failed: relocation failed: Undefined symbol: rt_dir_exists
```

The LSP MCP SMF artifact fails similarly in the same direct run lane.

## Why it matters

SMF execution starts in roughly 25-40 ms on this host, which is in the same
range as the Python/Bun MCP cold-stdio comparator. Source/script mode is still
roughly 60-330 ms:

```text
python3_mcp_median_ms=25-30
bun_mcp_median_ms=38-55
simple_mcp_script_median_ms=320-330
simple_lsp_mcp_script_median_ms=60-70
```

Using checked SMF artifacts is the architecture-preserving fast path listed in
the MCP startup guide, but the missing runtime symbol currently blocks it.

## Verification target

After the runtime symbol is exported/resolved for SMF, this should pass:

```bash
env SIMPLE_LIB=src bin/simple compile src/app/mcp/main.spl -o build/mcp-script/simple_mcp_server.smf
env SIMPLE_MCP_TOOL_SET=core SIMPLE_LIB=src bin/simple build/mcp-script/simple_mcp_server.smf < framed-init-tools-list.in
MCP_SCRIPT_PERF_USE_SMF=1 MCP_SCRIPT_PERF_STRICT=1 sh scripts/check/check-mcp-script-mode-perf.shs
```
