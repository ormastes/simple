# MCP SMF script artifact missing `rt_dir_exists`

Date: 2026-07-01

## Status

Partially fixed in source; deploy still blocked.

## Symptom

Compiling MCP script entrypoints to SMF succeeds. The first failing relocation
was:

```text
env SIMPLE_LIB=src bin/simple compile src/app/mcp/main.spl -o build/mcp-script/simple_mcp_server.smf
env SIMPLE_MCP_TOOL_SET=core SIMPLE_LIB=src bin/simple build/mcp-script/simple_mcp_server.smf

error: load failed: relocation failed: Undefined symbol: rt_dir_exists
```

The LSP MCP SMF artifact failed similarly in the same direct run lane.

`rt_dir_exists` is now implemented and registered in the Rust runtime symbol
table, along with the follow-on raw stdio symbols (`stdin_read_char`,
`print_raw`) and `text_dot_from_char_code`.

Bootstrap-built SMF smoke now reaches initialize/tools-list cleanly after
inlining/locally resolving startup helpers:

```text
simple_mcp_server.smf: rc=0, stderr=0, framed initialize/tools-list response
simple_lsp_mcp_server.smf: rc=0, stderr=0, framed initialize/tools-list response
```

The full `bin/simple` redeploy path still fails because Stage 4 self-hosted
native-build currently fails with:

```text
error: semantic: cannot parse '0.0' as i64
error: native-build worker exited with code 1 (no binary produced).
```

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
the MCP startup guide. Runtime relocation and startup helper resolution are no
longer blocked. Local MCP wrappers now prefer the checked SMF artifacts, and the
normal wrapper parity gate passes; full `bin/simple` redeploy remains blocked by
the Stage 4 native-build failure above.

## Verification target

After the runtime symbol is exported/resolved for SMF, this should pass:

```bash
env SIMPLE_LIB=src bin/simple compile src/app/mcp/main.spl -o build/mcp-script/simple_mcp_server.smf
env SIMPLE_MCP_TOOL_SET=core SIMPLE_LIB=src bin/simple build/mcp-script/simple_mcp_server.smf < framed-init-tools-list.in
MCP_SCRIPT_PERF_USE_SMF=1 MCP_SCRIPT_PERF_STRICT=1 sh scripts/check/check-mcp-script-mode-perf.shs
```
