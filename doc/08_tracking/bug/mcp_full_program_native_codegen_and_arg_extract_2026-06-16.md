# simple-mcp broken in Claude Code + bootstrap stage4 produces broken full CLI (2026-06-16)

Status: OPEN (bootstrap defect C and portability defect D remain)
Severity: P1 (self-hosted bootstrap deploy); native simple-mcp path resolved 2026-07-15
Owned-code scope: src/app/mcp, src/lib/nogc_sync_mut/mcp_sdk, seed/cranelift codegen, scripts/bootstrap

## 2026-07-15 MCP resolution update

The historical A/B evidence below is preserved, but it no longer describes the
current production MCP path:

- A fresh pure-Simple Stage 2 strictly native-builds
  `src/app/mcp/main.spl` to
  `build/bootstrap/mcp-package/simple_mcp_server` without stub fallback.
- The exact artifact now passes `initialize`, `notifications/initialized`, and
  `tools/list`, then serves argument-taking `simple_pipe` and `simple_search`
  calls in the pure-Simple system SSpec (3 examples, 0 failures).
- POSIX setup, MCP installers, and the Windows launcher now default to the
  cached native artifact. Exact overrides fail closed. Raw-source execution is
  explicit debugging only and may use only a deployed pure-Simple runtime.
- Defect A is resolved for current sources/artifacts. Defect B's old interpreter
  reproduction is not production mitigation and remains historical/unverified;
  native nested argument extraction is covered by the new feature-call cases.

Bootstrap defect C and LLVM detection defect D remain open and keep this issue
open.

## Summary

Two intertwined defects, both surfacing on **large/full Simple programs** built by the
current seed+cranelift toolchain. Smaller programs (bootstrap_main, simple_lsp_mcp,
trivial `print(1+1)`) are unaffected.

1. **simple-mcp tool calls fail in Claude Code.** The `simple-mcp` server connects
   (`initialize` + `tools/list` succeed) but every `tools/call` fails.
2. **`bootstrap-from-scratch.sh --deploy` ships a broken full CLI.** The seed→stage4
   (cranelift) build of `src/app/cli/main.spl` produces a binary that exits 248
   silently on any input.

## Repro & evidence

### A. native simple_mcp_server — tool dispatch broken (codegen)
Deployed/native binaries answer `initialize` and `tools/list` but break on `tools/call`:

- `build/bootstrap/mcp-package/simple_mcp_server` (Jun 13): returns
  `ERROR 2305843009213661350: Missing tool name` (graceful, isError) for ANY call.
- `bin/release/x86_64-unknown-linux-gnu/simple_mcp_server` (Jun 12): **core dumps**
  on `tools/list`/`tools/call`.
- Freshly bootstrap-built `build/bootstrap/full/.../simple_mcp_server` (this run):
  returns **empty** on `initialize`.

Request (standard MCP):
```
{"jsonrpc":"2.0","id":3,"method":"tools/call","params":{"name":"simple_status","arguments":{}}}
```
Source is correct (`src/app/mcp/main.spl:440-448`): `app_extract_obj(msg,"params")` then
`app_extract_str(params,"name")`. In the AOT-compiled binary the top-level `name`
extraction returns `""` → "Missing tool name". **The interpreter extracts it fine**
(`bin/simple run src/app/mcp/main.spl` → real result), so this is a native/AOT codegen
bug in JSON/string extraction on the full program, not a logic bug.

### B. MCP argument extraction broken even in the interpreter
Tools that take arguments fail with `Missing required parameter` in BOTH native and
interpreter — even directly, no bridge:
```
printf '%s\n%s\n' "$INIT" \
  '{"jsonrpc":"2.0","id":5,"method":"tools/call","params":{"name":"simple_read","arguments":{"path":"bin/simple_mcp_server"}}}' \
  | SIMPLE_LIB=src SIMPLE_MEMORY_LIMIT_MB=1024 bin/simple src/app/mcp/main.spl
# -> ERROR -32602: Missing required parameter: path
```
No-arg tools (`simple_status`) work in the interpreter. The failing path is the nested
args extraction: `app_extract_obj(params,"arguments")` (`mcp_sdk/server/app.spl:103`) and/or
`extract_field`→`_find_json_value_start` (`src/app/mcp/main_lazy_json.spl:89`). Both read
correct-looking; the failure is a runtime string/slice/`index_of`-with-offset behavior on
nested objects (same family as prior interpreter string bugs). NOT an obvious source fix.

### C. bootstrap stage4 — broken full CLI (cranelift on main.spl)
`scripts/bootstrap/bootstrap-from-scratch.sh --deploy` this run:
- Stage 3 self-host "fails" — EXPECTED (`bootstrap_main` lacks real codegen; "cannot emit
  a seed-wrapper fallback"). Script falls back to seed for stage 4.
- Stage 4 is forced to **cranelift** when using the seed (script lines 408-409). The
  seed+cranelift build of `main.spl` → 15 MB binary that exits **248 silently** on
  `-c 'print(1+1)'` (deterministic, 3/3). Trivial programs compiled by the same seed
  +cranelift run fine, so it is specific to the large program (codegen regression or a
  source regression in main.spl's dependency tree, in an actively-churned tree).
- The script aborts at the post-deploy smoke test under `set -e` (the broken binary's
  248 propagates) BEFORE the restore logic and MCP-deploy run — so a broken `bin/simple`
  was left live (now restored; see Mitigation).
- The prior working binary is **461 MB** vs the broken **15 MB** (~30×), suggesting the
  last good build came from a different path (likely LLVM-featured), not seed+cranelift.

Broken binary preserved: `bin/release/x86_64-unknown-linux-gnu/simple.broken_stage4_248`.

Additional evidence from the LLM runtime-control lane on 2026-06-26:

- Command:
  `timeout 300s release/x86_64-unknown-linux-gnu/simple native-build --source
  src/app --source src/lib --entry-closure --entry src/app/cli/main.spl --strip
  --threads 1 --timeout 240 --output build/llm_runtime/simple_cli_full`
- Result: exit `124`, no `build/llm_runtime/simple_cli_full` binary emitted.
- Observed progress reached compiler/backend modules before the external cap.
  Diagnostics included existing full-program warnings such as ambiguous
  `ConstEvaluator.*.to_text` candidates and private helper collisions, but no
  focused vLLM control source failure.
- Impact for `llm-runtime-control`: standalone native app evidence exists, and
  the top-level source registration is covered by SPipe specs, but full rebuilt
  top-level `simple llm-runtime-control` binary evidence remains blocked by the
  full-program native build lane.

### D. (minor, orthogonal) macOS-only LLVM-18 detection
`bootstrap-from-scratch.sh:227` only checks `/opt/homebrew/opt/llvm@18`. This Linux host
has LLVM 18.1.8 at `/usr/lib/llvm-18` (`lib/libLLVM-18.so`), so it always falls back to
cranelift. Fixing detection does NOT fix (C): stage 4 forces cranelift when using the seed
regardless of backend. Worth fixing separately (probe `llvm-config-18 --prefix` /
`/usr/lib/llvm-18` on Linux).

## Impact
- The former simple-mcp native tool-call impact is resolved by the 2026-07-15
  pure-Stage2 artifact and system-test evidence above.
- `--deploy` cannot produce a working self-hosted CLI on this host via the current path.

## Historical mitigations applied in the original session
- Restored the prior working `bin/release/<triple>/simple` (461 MB) after `--deploy` left
  the broken 248 binary live. `bin/simple -c 'print(1+1)'` → 2 again.
- `bin/simple_mcp_server`: added a source-mode memory floor (100 MB tripped the RSS
  watchdog immediately for the interpreter, which needs ~102 MB just to load) and an
  opt-in `SIMPLE_MCP_FORCE_SOURCE=1` escape hatch. NOTE: source mode only partially works
  (no-arg tools only — see B) and the no-GC interpreter leaks, so it is NOT wired as the
  default; it is an operator/debug escape hatch until B is fixed.
- `config/mcp/install.shs`: resolve both MCP native binaries from the canonical deploy dir
  (commit 67ab978) — correct for a healthy repo; does not address the codegen bugs here.

## Suggested fix order
1. Fix the bootstrap smoke-test `set -e` gap so a failing stage4 binary triggers the
   restore path instead of aborting the script before it.
2. Root-cause the remaining full-program Stage 4/cranelift failure (C).
3. Fix Linux LLVM-18 detection (D).
4. Keep the exact native MCP build/handshake/feature SSpec as the regression gate;
   investigate the historical interpreter-only nested-argument repro separately
   if source debugging becomes a supported production lane.
