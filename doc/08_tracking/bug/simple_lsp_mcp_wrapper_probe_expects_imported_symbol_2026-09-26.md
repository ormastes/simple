# `simple-lsp-mcp` can never be recovered: its wrapper probe asserts a symbol the server never reports

- **Filed:** 2026-09-26
- **Status:** FIXED 2026-09-26 — BOTH sides were wrong, and both broke in the same merge
  (`e274cd33719`, 2026-08-27). See "Resolution" at the end.
- **Area:** `scripts/setup/setup.shs` (generates `bin/simple_lsp_mcp_server`) /
  `src/app/simple_lsp_mcp` `lsp_symbols`
- **Host:** yoon-note, x86_64-unknown-linux-gnu

## Summary

A native `simple_lsp_mcp_server` CAN now be built (it could not this morning — every
`native-build` exited 132/SIGILL until
`seed_cranelift_bare_return_in_inferred_any_fn_traps_2026-09-26.md` was fixed). The
built server is genuinely functional. It still cannot be admitted, because the
wrapper's probe requires a symbol that the server does not emit — and the
source-run server, which the repo's own tool gate certifies as PASS, does not emit
it either.

## The probe, and exactly which assertion fails

`bin/simple_lsp_mcp_server` (generated) probes a candidate with three
newline-delimited requests — note NOT `Content-Length` framed, and string ids:

```
{"jsonrpc":"2.0","id":"1","method":"initialize", ...}
{"jsonrpc":"2.0","id":"2","method":"tools/list","params":{}}
{"jsonrpc":"2.0","id":"3","method":"tools/call","params":{"name":"lsp_symbols",
   "arguments":{"file":"src/app/simple_lsp_mcp/main.spl"}}}
```

and requires all of:

| assertion | result |
|---|---|
| `"id":"1"` has `result`, no `error` | **ok** |
| `"id":"2"` result contains `lsp_symbols` | **ok** |
| `"id":"3"` has `result` with `content[].type=text` | **ok** |
| that text contains `\"name\":\"log_options_help\"` | **FAILS** |
| `"id":"3"` has no `error` / `isError` / `command failed with exit code` | ok |

Only the fourth fails. The failure is reported as
`native_probe_failed ... reason=initialize_list_or_symbols_call_failed`, and after all
candidates fail the wrapper prints `error: native simple_lsp_mcp_server not found`
— which is misleading: the binary IS found, it fails its probe.

## Why this is not a build problem

`log_options_help` is an **imported** name, not a declaration in the file:
`src/app/simple_lsp_mcp/main.spl:14` has
`use std.cli.log_modes.{parse_log_options, log_options_help, render_progress}`.
`lsp_symbols` returns only in-file declarations, beginning at `SERVER_NAME` (line 16)
and skipping the imports on lines 13-14.

Measured across three independent builds of the same source:

| build | `id:3` result | `log_options_help` |
|---|---|---|
| AOT, `--source src/app/simple_lsp_mcp --source src/app/io` | present, real symbols | absent |
| AOT, same plus `--source src/lib` | present, **zero** symbols | absent |
| **source-run** (`simple run src/app/simple_lsp_mcp/main.spl`) | present, real symbols | absent |

The third row is the important one: that is the configuration
`scripts/check/build-and-verify-tools-with.shs` certifies as
`PASS simple_lsp_mcp — MCP initialize handshake OK`. So the assertion is not an AOT
regression; **no build of the current source can satisfy it.**

Also of note: adding `--source src/lib` made `lsp_symbols` return zero symbols. That
is a second, separate defect worth its own look — a wider source set should not empty
the symbol list.

## Two ways to fix — this is an owner decision, not a code cleanup

1. **The server is wrong:** `lsp_symbols` is supposed to report imported bindings as
   document symbols, and regressed. Then fix `lsp_symbols`, and the probe is correct
   as written.
2. **The probe is wrong:** document symbols are declarations only, imports were never
   meant to appear, and the assertion encodes an expectation from a different
   implementation. Then the probe's `log_options_help` check must be replaced with a
   symbol the server genuinely emits (e.g. `SERVER_NAME`).

Determining which requires knowing the intended contract of `lsp_symbols`, which is
why it is not resolved here. **Do NOT simply delete or weaken the assertion to get a
green server** — it is the only thing standing between a real server and a silently
non-functional one, and the previously deployed artifact shows why that matters (see
below).

## State left behind

Nothing was deployed. The pre-existing artifact
(`bin/release/{x86_64-unknown-linux-gnu,linux-x86_64}/simple_lsp_mcp_server`,
2,995,736 bytes, 2026-09-26 13:00, one inode across both entries) was restored
byte-for-byte with a verified matching `.sha256` sidecar (`sha256sum -c` -> OK).

That restored artifact is itself broken in a DIFFERENT way, recorded so it is not
mistaken for working: its `process_run_bounded` child spawn returns **-1** warm and
cold, and `tools/lsp-mcp-registry/native/simple_lsp_mcp_server` SEGVs (rc=139). So
`simple-lsp-mcp` is currently down for two independent reasons, and the wrapper
correctly refuses to serve either. A wrapper that fails closed is right; do not add a
stub or set `SIMPLE_MCP_FULL` to bypass it.

## The build recipe, for whoever picks this up

The interpreted pure-Simple driver lane cannot build real programs today (it rejects
unannotated non-`main` functions with `E-SFFI-016: missing return in non-unit
function`, reproducible on a 12-line hello world). The working route is the Rust
native pipeline, which `bootstrap-phase-verification.shs:739` also uses:

```
SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_BOOTSTRAP=1 SIMPLE_RUST_SEED_WARNING=0 \
  src/compiler_rust/target/release/simple native-build --backend cranelift \
  --source src/app/simple_lsp_mcp --source src/app/io \
  --entry src/app/simple_lsp_mcp/main.spl --entry-closure \
  --cache-dir <cache> -o <out>
# rc=0, ~180 KB, answers initialize + tools/list + a real lsp_symbols call
```

## Resolution (2026-09-26)

Evidence on the `lsp_symbols` contract: it is **declarations-only by design**.
`query_visibility_symbols` (`src/app/cli/_QueryVisibility/query_commands.spl:166`) calls only
`parse_symbols_in_file(clean_file)`; the import walk at lines 146-158 belongs to the
`completions` subcommand. At `8401b5ebfd3` (2026-07-23, the commit that wrote the probe)
`main.spl:33` DECLARED `fn log_options_help()` locally, so the assertion was true when
written. The `e274cd33719` merge (2026-08-27) moved it into `std.cli.log_modes` (an import)
without updating the probe. So the probe was stale, not the server.

A second defect hid behind the first: the same merge changed `make_tool_result`,
`make_tool_error` and `jsonrpc_error` in `src/app/simple_lsp_mcp/json_helpers.spl` from
`js(x)` to `js(escape_json(x))` — but `js()` already escapes, so every payload was
double-escaped (`\\\"name\\\"`, byte-identical on AOT and source-run, 44,952 bytes). The
probe's single-escaped `\"name\":\"...\"` could therefore never match ANY symbol; swapping
in `SERVER_NAME` alone would still have failed. Sibling `simple-mcp` never had this
(`src/app/mcp/api_tools.spl:389` is `js(content)`).

Fixes: `json_helpers.spl` three sites -> `js(x)`; `scripts/setup/setup.shs` probe ->
`\"name\":\"SERVER_NAME\"` (a declared symbol, still requires real content) and
`_LSP_MCP_PROBE_WRAPPER_VERSION` bumped to `0.9.14-declared-symbol-probe` so stale stamps
re-probe; `scripts/check/check-mcp-wrapper-contract.shs` fixtures updated to the same
symbol. Specs: `test/01_unit/app/simple_lsp_mcp/json_helpers_spec.spl` (reproduction on
`make_tool_result`, generalization on `make_tool_error`; `executed=4 passed=4`).
After the fix the same probe yields 36,368 bytes with single-escaped names. Deployed
(179,584 bytes, one inode across both release entries, sidecars verified).

Still open, separately: `tools/lsp-mcp-registry/native/simple_lsp_mcp_server` is a
git-tracked 2026-09-02 binary that SEGVs; and `--source src/lib` emptying the symbol
list (noted above) was not investigated here.

## Related

- `seed_cranelift_bare_return_in_inferred_any_fn_traps_2026-09-26.md` — the SIGILL fix
  that made building this possible at all.
- `doc/07_guide/app/mcp/mcp.md` § Troubleshooting and `.claude/rules/code-style.md`
  (deploy needs both directory entries as one inode plus a refreshed `.sha256`, or the
  wrapper rejects the binary).
