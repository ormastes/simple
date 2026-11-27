# MCP SMF script artifact missing `rt_dir_exists`
## Resolved — symbol exported; note 2026-11-25

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

Date: 2026-07-01

## Status

Resolved. `rt_dir_exists` is exported and registered (fix `cc7be21a66f`);
the bug_db row is `closed`. The separate Stage 4 native-build redeploy
blocker is tracked in
`native_build_stage4_pre_object_spin_2026-07-13.md`.

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


## Verification 2026-11-25 (lane p2w3-ai)

The title defect — SMF relocation failing on undefined `rt_dir_exists` — is
fixed in tree: commit `cc7be21a66f` ("fix: export rt_dir_exists for MCP SMF
path") landed the runtime export, and the symbol is registered in the Rust
runtime symbol table (`src/compiler_rust/common/src/runtime_symbols.rs`) and
the interpreter extern dispatch
(`src/compiler_rust/compiler/src/interpreter_extern/file_io.rs`). The bug_db
row has been `closed` since 2026-08-17. The doc's remaining blocker was never
this symbol: it was the Stage 4 self-hosted native-build failure
(`cannot parse '0.0' as i64`), owned by
`native_build_stage4_pre_object_spin_2026-07-13.md` / TODO 535.

A fresh run of the verification target (`bin/simple compile ... .smf` +
`check-mcp-script-mode-perf.shs`) is environment-blocked in this lane: the
pinned `bin/simple.exe` seed rejects `@representation_boundary` tree-wide at
HEAD, so no compile/test command runs. Closure of THIS row rests on source
inspection of the exported symbol plus the recorded bootstrap-SMF smoke
results above (initialize/tools-list rc=0 for both servers).
