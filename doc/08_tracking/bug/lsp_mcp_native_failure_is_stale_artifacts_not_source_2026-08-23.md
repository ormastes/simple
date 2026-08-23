# Bug: "native LSP MCP is broken" is STALE ARTIFACTS, not a live source defect

- **Filed:** 2026-08-23
- **Severity:** P3 (was reported as a P1 bootstrap blocker; measurement says otherwise)
- **Components:** `bin/release/*/simple_lsp_mcp_server` (artifacts), `bin/simple_lsp_mcp_server`
  (generated wrapper), `scripts/setup/setup.shs`
- **Supersedes (for the native half):**
  `doc/08_tracking/bug/lsp_mcp_native_arg_extract_and_source_diagnostics_deadlock_2026-06-18.md`
  defect 1

## Verdict

The 2026-06-18 defect 1 ("native `tools/call` always returns `Missing tool
name`") is **NOT present in current source**. Every observed failure on this
machine is a stale build artifact. No source patch was made, because no source
defect was found.

## Evidence

### Current source passes the Stage 5 contract end to end

Executed with the seed the running bootstrap had just built
(`src/compiler_rust/target/bootstrap/simple`, 130,272,000 B, mtime 2026-08-23
17:28, copied to scratchpad and run from the copy), fed the byte-exact framed
input that `scripts/check/check-mcp-native-smoke.shs:123-145` sends
(initialize / notifications-initialized / tools/list / `tools/call` `lsp_symbols`
on `src/app/simple_lsp_mcp/main.spl`), rc read into a variable on the line after
the invocation:

```
rc=0
"id":"3","result":{"content":[{"type":"text","text":"[{\"name\":\"SERVER_NAME\",...
```

Fed to the real validator, `scripts/check/validate_mcp_native_smoke.spl`:

```
lsp_tools_json_valid=true
lsp_framing_valid=true
lsp_tools_schema_valid=true
lsp_correlated_ids_valid=true
lsp_main_feature_call_valid=true     <- this is lsp.feature_valid at :341
lsp_tools_count=12
```

Both marker strings the two probes look for are present in the id-3 payload:
`\"name\":\"main\"` (validator, `validate_mcp_native_smoke.spl:273`) and
`\"name\":\"log_options_help\"` (the newer wrapper probe, `setup.shs:485`).

This proves the source *logic* — `detect_tool_name` -> `arg_field` ->
`_find_json_value_start` — is correct. It does **not** prove the AOT/native
lowering of that logic is correct; see Limits.

### The failing artifacts predate the source correction

| artifact | size | mtime | probe result |
|---|---|---|---|
| `bin/release/aarch64-apple-darwin/simple_lsp_mcp_server` | 20,861,560 | 2026-07-11 20:47 | `Missing tool name` (defect 1 shape) |
| `bin/release/aarch64-apple-darwin-macho/simple_lsp_mcp_server` | 153,620,472 | 2026-04-23 14:57 | **passes** the functional call; v0.2.0 server |

The Jul 11 binary predates the 2026-07-16 `json_helpers.spl` correction
(recorded in the 06-18 bug's "2026-07-16 hardening evidence" section); source has
moved repeatedly since (`git log` on `json_helpers.spl` / `tools.spl`: 08-01,
08-08, 08-10, 08-11). Nothing on disk was built from current source.

### The wrapper rc=127 is a 3-second timeout straddle, also stale

`SIMPLE_LSP_MCP_PREFER_NATIVE=1 bin/simple_lsp_mcp_server` -> rc=127. Cause:
the *deployed* wrapper is `simple_lsp_mcp_server:0.9.9-tools-call` with
`SIMPLE_LSP_MCP_NATIVE_PROBE_TIMEOUT:-3` (`bin/simple_lsp_mcp_server:75,124`),
and the macho candidate's probe takes **2.89 / 3.28 / 3.63 s** (three runs,
`/usr/bin/time -p`). With `SIMPLE_LSP_MCP_NATIVE_PROBE_TIMEOUT=30` the same
wrapper selects that binary and exits 0.

This is already fixed in the generator: `scripts/setup/setup.shs:429,479` emits
`simple_lsp_mcp_server:0.9.13-cwd-symbols-call` with a **30 s** default and a
stricter probe. The deployed wrapper is simply older than the generator and is
rewritten verbatim on the next `setup.shs` run. No edit to `setup.shs` is
warranted.

## Difference from the working `simple_mcp_server` (asked, for the record)

Same manual-scanner algorithm on both sides; the primitives differ.
`src/app/mcp/main_lazy_json.spl:9-12,83-108` uses `s.substring(start,end)`,
`index_of`-driven scanning, and a bounds-checked `_char_at`;
`src/app/simple_lsp_mcp/json_helpers.spl:66-94` uses bracket slicing
`s[start:end]`, a hand-rolled scan loop, and an unchecked `_char_at`. Also
`main.spl:419-429` extracts `params` before `name`, where the LSP server searches
the whole body. None of this is currently observable as a defect — the LSP path
is green under the interpreter — so nothing was changed. But the comment at
`json_helpers.spl:66-70` claiming "the full-program native MCP path proves direct
text slicing" is factually wrong: the MCP sibling uses `.substring`, not
`[a:b]`. If a fresh native build *does* regress to `Missing tool name`, aligning
`_slice_text`/`_char_at` with the MCP sibling's proven primitives is the first
thing to try.

## Limits of this verification

- The check ran on the **interpreter**, not AOT. The historical defect was an
  AOT-lowering defect, so this is source-correctness evidence, not native
  evidence.
- A scratch native build was attempted and **could not be produced**: the only
  compiler available (`bin/release/aarch64-apple-darwin-macho/simple`,
  132,398,344 B, mtime 2026-08-10 09:00) fails on current `src/lib` with
  `llvm codegen: semantic: llvm global load referenced undeclared symbol 'ffi'`
  across `io_runtime.spl`, `io/file_ops.spl`, `io/process_ops.spl`,
  `io/signal_stubs.spl`. Stage 5 uses the fresh stage binary, which this host did
  not yet have.

## Action

None on source. Rebuild and redeploy; re-probe the fresh artifacts. If Stage 5
aborts on `lsp.feature_valid` with a genuinely fresh binary, that is a **new**
observation about native lowering and should be filed as such, not attributed to
the 06-18 record.
