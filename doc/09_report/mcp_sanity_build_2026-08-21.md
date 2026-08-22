# MCP Server Sanity Build + Handshake — 2026-08-21

Goal: a sanity build of the MCP server and a passing `initialize` + `tools/list`
exchange, independent of the stage1 bootstrap.

Base: `origin/main` (worktree `/mnt/data/worktrees/mcpbuild`, detached).
Compiler used: deployed Rust seed
`/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`
(bootstrap seed; the pure-Simple full CLI is not deployed).

## 1. Build

Build path per `doc/07_guide/app/mcp/mcp.md`:

```
SIMPLE_CACHE_SCOPE=mcp simple native-build --runtime-bundle core-c-bootstrap \
  --source src/app --entry-closure --entry src/app/mcp/main.spl \
  --strip --threads 2 --output build/mcp-sanity/simple_mcp_server
```

| target | wall | result |
|---|---|---|
| `simple_mcp_server` (attempt 1) | 1213.97 s | FAIL — HIR lowering, `text_advanced.spl` |
| `simple_lsp_mcp_server` (attempt 1) | 434.90 s | FAIL — same |
| `simple_mcp_server` (attempt 2, after fix) | 1972.13 s | FAIL — `undefined field 'kind'` |
| `simple_lsp_mcp_server` (attempt 2, after fix) | — | FAIL — `undefined field 'kind'` |

**Verdict: no fresh MCP binary was produced.** Two blockers, one fixed, one open.

### Blocker 1 — FIXED (`5c285c2436f`)

```
error: HIR lowering error in src/lib/common/text_advanced.spl:
  untyped function returns a value: function 'dedent_lines' returns a value
  but declares no return type; add '-> T'
```

Six functions were affected: `dedent_lines`, `detect_indent`, `hamming_distance`,
`longest_word`, `most_common_char`, `normalize_indent`. This broke **every**
`--entry-closure` native-build whose closure reaches `std.common`, not just MCP.

Fix: added the missing return types (`(text, i64)?`, `i64`, `[text]`, `i64?`) and
made `most_common_char`'s accumulators type-stable by seeding them from
`freqs[0]` instead of `nil`.

Reproduce spec: `test/01_unit/lib/common/text_advanced_return_types_spec.spl`
— 6 examples covering all six functions including their nil/optional paths.
Pre-fix the build failed at HIR lowering; post-fix the spec is 6/6 green and the
`text_advanced` diagnostics are gone from the build log (verified: 0 occurrences).

### Blocker 2 — PARTLY FIXED, still OPEN

```
error: semantic: undefined field 'kind': cannot access field on value of type 'nil'
```

Hit by **both** entries (`src/app/mcp/main.spl` and `src/app/simple_lsp_mcp/main.spl`),
so it lives in shared code reached through the entry closure, or in the driver.

Two things make it hard, and both are defects in their own right:

1. **The diagnostic carries no file/line span.** It is the only error printed.
2. It fires *after* every instrumented source reports clean —
   `[bootstrap-error-count] source_idx=2 point=post-store count=0` is the line
   immediately before it — so it is not a plain source-compile error but
   something on the post-store entry-closure / codegen path.

Full stderr preserved at `/mnt/data/tmp/native-build-stderr-359022.log`
(the driver truncates 16945 of 28945 bytes from the middle of worker stderr,
which is a third obstacle to diagnosis).

## 2. Handshake

Harness: three newline-delimited JSON-RPC messages (`initialize`,
`notifications/initialized`, `tools/list`) piped to the server over stdio.

Since no fresh binary exists, the exchange was run against the **already-deployed**
native artifact and against **source mode**, to establish the baseline the fresh
build must reproduce.

`bin/release/linux-x86_64/simple_mcp_server` (8014312 bytes, dated 2026-08-11):

```json
{"jsonrpc":"2.0","id":1,"result":{"protocolVersion":"2025-06-18",
 "capabilities":{"tools":{"listChanged":true},"resources":{"listChanged":false},
 "prompts":{"listChanged":false},"logging":{},"roots":{"listChanged":false}},
 "serverInfo":{"name":"simple-mcp-full","version":"4.0.0"}}}
```

```json
{"jsonrpc":"2.0","id":2,"result":{"tools":[
  {"name":"simple_pipe","description":"[query] SPipe-linked codebase, context, and Ponytail surface", ...},
  {"name":"simple_search", ...},
  {"name":"node_repl", ...}]}}
```

Source mode (`simple src/app/mcp/main.spl`) returns the **same** `serverInfo`
and the **same** 3 tools, so the deployed artifact is consistent with source.

**Handshake verdict: PASS** — valid `initialize` result, non-empty tools array,
native artifact and source mode agree.

Note: `doc/07_guide/app/mcp/mcp.md` opens with "currently provides 151 tools".
Both the deployed binary and source mode return **3**. The three are aggregate
dispatch surfaces (`simple_pipe` fans out over spipe/context/codebase/search/
ponytail), so the count is not necessarily a regression — but the guide's
figure is stale and should be reconciled with the tool table.

## 3. Deploy

**Not performed.** Deploying requires a freshly built artifact; blocker 2
prevented one. The existing deployed servers were left untouched.

## 3b. Update — blocker 2 localized, two traps fixed, one open

The span-less error was localized using the seed's **existing**
`SIMPLE_DEBUG_FIELD_ACCESS=1` instrumentation (no rebuild needed), which prints
the receiver expression and a Simple-level call stack:

```
[field-access-error] field=kind recv_type=nil recv=nil expr=Identifier("t")
  stack=... -> run_any_escape_pass -> any_check_function -> any_check_block
     -> any_check_stmt -> any_type_is_any
```

Two traps of the same class were fixed and landed (`f1cf8081849`):

- `35.semantics/any_escape/checker.spl`, `any_check_stmt` `case Let`: the
  declared type is absent for an inferred `val x = e`, and `any_type_is_any`
  opens with `match t.kind`. Now unwrapped with `if val`.
- `20.hir/.../module_callable_types.spl`, `declared_callable_type`: `Param.type_`
  passed to `lower_type` with no `has_type_` guard (its sibling guards). Latent,
  not the blocker.

Evidence: any_escape suite 14/14; new
`test/01_unit/compiler/hir/untyped_param_declared_callable_type_spec.spl` 5/5.

**Still open:** with the nil receiver gone, the build now fails with
`undefined field: unknown property or method 'kind' on Option` — the same shape
on a *wrapped* optional, at a different site. That arm of the interpreter
(`calls.rs:1032`) has no debug branch, so it cannot be localized the same way
until one is added. Details and candidate sites are in the bug record.

Also corrected: the original "fires after post-store" reading was wrong —
`[bootstrap-error-count]` is capped at `source_idx < 3`.

## 4. Verdict

- Build: **FAIL** — three root causes found, two fixed and landed, one open.
- Handshake: **PASS** against the deployed artifact and source mode.
- Deploy: **not done**, blocked on the build.

The milestone is not met: the sanity build does not yet produce a binary. The
handshake half is proven and the harness is ready to re-run the moment the last
trap is cleared. Iterate on the LSP entry (~7.5 min), not the MCP entry (~33 min).
