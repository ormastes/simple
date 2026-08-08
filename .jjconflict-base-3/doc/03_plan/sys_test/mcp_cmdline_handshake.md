# MCP Command-Line Handshake Test Plan

## Scope

Validate the pure-Simple MCP server by building the exact native entry with
fresh pure Stage 2, launching it as a command-line process, sending an MCP
initialize/initialized/tools-list handshake, and requiring a bounded response.
Bootstrap acceptance also launches the exact Stage 5 MCP/LSP output pair once
before deploy; compiler Stages 2 through 4 do not duplicate the probe.

## Helper Contract

The system spec helper builds JSONL MCP messages, writes them to a temporary
stdin file, launches the exact native artifact, and verifies:
- `--json` readiness contains the expected server marker.
- Command exits with status `0`.
- Elapsed time is under `15000 ms`.
- Output contains JSON-RPC initialize and tools/list responses.
- Output contains a representative expected tool marker.
- Output does not report parse errors or native-missing failures.
- Feature responses preserve request IDs, contain semantic results, and contain
  neither JSON-RPC errors nor MCP `isError` results.

The helper is pure Simple spec code using stdlib process, file, env, and time
helpers. It must not declare direct `rt_*` externs and must not require Node.js.

The scenario executes the exact
`build/bootstrap/mcp-package/simple_mcp_server` artifact directly. It exercises
`simple_pipe` readiness and the bounded no-match behavior of `simple_search`;
a `bootstrap-only` or `mode=source` marker fails the scenario. The wrapper-template
contract separately requires cached-native default execution and explicit-only
pure-Simple source fallback.

## Pass Criteria

The freshly built exact artifact answers the handshake within the time limit,
lists tools, and serves both representative feature calls.
The Stage 5 gate additionally requires successful `simple_status`,
`simple_pipe` codebase, and `lsp_symbols` calls from the exact freshly built
pair. `--no-mcp` is an explicit skip and supplies no MCP acceptance evidence.

## Current Risk

Native artifact health is part of the contract. If the pure Stage 2 build fails
or the child process segfaults, the system spec fails; that is a server/package
bug, not a test-helper pass.

## Current State — 2026-07-24

- `1d5b3d3f6a0d` strengthened native admission and smoke coverage. The wrapper
  now probes a real `simple_pipe` search, and the paired smoke requires
  `simple_status` plus `simple_pipe(surface=codebase, query=main, scope=app)`.
- The installed Linux artifact passes initialize/tools-list and
  `simple_status`, but the codebase call exits `139`. GDB isolates the fault to
  `_process_run_inherit -> rt_process_run -> shell_cmd ->
  _simple_pipe_search_text`; therefore it is stale and must not be admitted.
- A fresh self-hosted Stage 4 compiler at
  `/tmp/simple_riscv_prod_main_20260723/build/stage4-ufcs/stage4-clean/simple`
  (`sha256 ed5bdd70ca3c51f842b92fce3521014a005507e60be8adb8cb16f4d436477680`)
  reached the MCP link with `SIMPLE_NO_STUB_FALLBACK=1`.
- Explicit imports removed all five unresolved `_mcp_find_simple_binary`
  callers. Canonical `Dict<text, any>` annotations preserve JSON object
  receiver provenance; the focused source regression pins all three
  `map.has(key)` sites.
- The pure-Simple runtime archive completed at
  `/tmp/root-mcp-current-llvm-20260724-1/simple-core/libsimple_runtime.a`.
  The third bounded MCP build stopped because this Stage 4 CLI did not honor
  `--runtime-path`; it requires the runtime directory through
  `SIMPLE_RUNTIME_PATH` and the exact archive through
  `SIMPLE_CORE_RUNTIME_PATH`. The session retry cap is exhausted. No further
  native retry is permitted in this session.

## Ordered Remaining Work

1. **Complete:** `ecaefd1be7aa` committed and synced the reviewed MCP
   helper-import, typed-JSON receiver, runtime-path plumbing, tests, and this
   plan.
2. In a fresh session, build and fully smoke the simple-core runtime once per
   backend into separate directories. Require the archive-symbol gate, hello,
   C5 exact exit `42`, TUI markers, and closure-clean result.
3. Build one fresh LLVM MCP artifact with the runtime environment set
   explicitly:

   ```bash
   FRESH_SIMPLE=/path/to/current/pure-simple
   CORE_DIR="$PWD/build/c5-core-archive-llvm"
   env SIMPLE_LIB=src SIMPLE_NO_STUB_FALLBACK=1 \
     SIMPLE_RUNTIME_PATH="$CORE_DIR" \
     SIMPLE_CORE_RUNTIME_PATH="$CORE_DIR/libsimple_runtime.a" \
     "$FRESH_SIMPLE" native-build --backend llvm \
       --runtime-bundle simple-core \
       --source src/compiler --source src/app --source src/lib \
       --entry-closure --entry src/app/mcp/main.spl --strip \
       --cache-dir build/c5-mcp-stage4-llvm-cache \
       --output build/c5-mcp-stage4-llvm/simple_mcp_server
   ```

   Pass requires exit `0`, a nonempty executable, no unresolved helper,
   `Dict.has`, runtime-provider, or stub-fallback symbols, and a link receipt
   naming the selected simple-core archive.
4. Drive the new artifact directly through initialize, initialized, tools/list,
   `simple_status`, and `simple_pipe` codebase query. Require correlated IDs,
   the `-- simple_pipe codebase query=main --` marker, and no signal/exit `139`.
5. Build the matching LSP MCP artifact with a separate cache, then run the
   exact fresh pair once:

   ```bash
   env SIMPLE_BINARY="$FRESH_SIMPLE" \
     MCP_SERVER="$PWD/build/c5-mcp-stage4-llvm/simple_mcp_server" \
     LSP_MCP_SERVER="$PWD/build/c5-mcp-stage4-llvm/simple_lsp_mcp_server" \
     MCP_NATIVE_BOOTSTRAP_FRESH=1 \
     sh scripts/check/check-mcp-native-smoke.shs
   ```

6. Build the release/package pair on the required core-C bootstrap lane, then
   deploy only checksum-matched Linux artifacts and sidecars:

   ```bash
   "$FRESH_SIMPLE" native-build --runtime-bundle core-c-bootstrap \
     --source src/compiler --source src/app --source src/lib --entry-closure \
     --entry src/app/mcp/main.spl --strip \
     --output build/bootstrap/mcp-package/simple_mcp_server
   "$FRESH_SIMPLE" native-build --runtime-bundle core-c-bootstrap \
     --source src/compiler --source src/app --source src/lib --entry-closure \
     --entry src/app/simple_lsp_mcp/main.spl --strip \
     --output build/bootstrap/mcp-package/simple_lsp_mcp_server
   ```

   Regenerate the production wrappers, prove the real search probe admits the
   new hash, and capture startup/request latency and RSS with
   `check-mcp-lsp-nfr-evidence.shs`. The simple-core build in step 3 is runtime
   migration evidence; it does not replace these release artifacts.
7. Stage both npm registry payloads from verified release assets and require
   both dry runs to list the declared Linux/x64 native executable:

   ```bash
   sh scripts/check-mcp-release-assets.shs tools/mcp-registry
   sh scripts/check-mcp-release-assets.shs tools/lsp-mcp-registry
   (cd tools/mcp-registry && npm pack --dry-run)
   (cd tools/lsp-mcp-registry && npm pack --dry-run)
   ```

8. Before deploy, run the current pure runtime checks for `src/compiler`,
   `src/lib`, `src/app/mcp`, and `src/app/simple_lsp_mcp`; run
   `test/02_integration/app/mcp_stdio_integration_spec.spl` in interpreter
   mode, the core runtime smoke, and both working/staged direct-env guards.

Follow-up platform work: make POSIX wrapper candidate selection host-triple
aware for macOS, and make Windows MCP/LSP wrappers native-only with SHA and
real tools/call admission. These do not replace the Linux release blockers
above.

## Execution

```bash
# Prerequisite: fresh pure Stage 2 and Stage 3 (the SSpec performs the strict
# exact-entry MCP native-build itself).
SIMPLE_NO_STUB_FALLBACK=1 sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --pure-simple --no-mcp --jobs=half
bin/simple check test/03_system/app/mcp_cmdline/mcp_cmdline_handshake_spec.spl
bin/simple test test/03_system/app/mcp_cmdline/mcp_cmdline_handshake_spec.spl --native
```

## Traceability

| REQ | Description | Test File | Generated Spec | Coverage |
|-----|-------------|-----------|----------------|----------|
| REQ-MCP-CMD-001 | A pure-Stage2-built native Simple MCP answers initialize/tools-list and serves core tool calls within a time limit | `test/03_system/app/mcp_cmdline/mcp_cmdline_handshake_spec.spl` | `doc/06_spec/03_system/app/mcp_cmdline/mcp_cmdline_handshake_spec.md` | Full |
| REQ-MCP-CMD-002 | Fresh Stage 5 MCP/LSP outputs answer correlated handshakes and successful `simple_status`, `simple_pipe` codebase, and `lsp_symbols` calls before deploy | `scripts/check/check-mcp-native-smoke.shs` | `doc/07_guide/tooling/mcp_handshake_regression.md` | Gate complete; fresh current-artifact execution and deploy evidence pending |
