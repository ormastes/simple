# LSP MCP: integer position args (line/character) corrupted in deployed server

- **Status:** Open
- **Severity:** P1 (7 of 11 LSP MCP tools unusable)
- **Date:** 2026-06-14
- **Component:** `src/app/simple_lsp_mcp/` (compiled `simple_lsp_mcp_server`)

## Symptom

Live MCP calls against the deployed `bin/release/.../simple_lsp_mcp_server`:

| Tool | Result |
|------|--------|
| `lsp_symbols` | ✅ works (fixed separately — entry-point) |
| `lsp_diagnostics` | ✅ works |
| `lsp_completion` | ✅ returns a list (but position-independent — see note) |
| `lsp_hover` | ⚠️ returns `null` |
| `lsp_definition` | ❌ `No symbol found at <file>:740116738` |
| `lsp_references` | ❌ `No symbol found at <file>:740323010` |
| `lsp_document_highlight` | ❌ `…:740537890` |
| `lsp_type_at` | ❌ `…:740743906` |
| `lsp_type_definition` | ❌ `…:740952898` |
| `lsp_implementation` | ❌ `…:741163762` |
| `lsp_signature_help` | ❌ `…:741865010` |

Split is exact: **every tool that passes an integer `line`/`character` is broken; every
string-only tool works.** The **file path arrives intact** (`<file>:` part is correct); only
the integer `line_num` is garbage. The garbage value is **monotonically increasing across
calls** (740116738 → 740323010 → …, ~200K/call) — a parse bug would be deterministic per
input; a growing pointer-/offset-like value indicates the integer is being read from
uninitialized/heap memory in the running process.

`lsp_completion` only appears to work because `query_visibility_completions` returns the full
identifier+keyword list regardless of position; it does not prove `line0` is correct.
`lsp_hover` → `null` is consistent with a garbage line (out-of-range → no symbol).

## What is NOT the cause (ruled out)

- **Stale binary** — `simple_lsp_mcp_server` (Jun 13 00:12) is newer than the last
  `simple_lsp_mcp/` source commit (`b0f2319cba4`, Jun 12 03:50). Built from current source.
- **Backend bug** — `lsp_query.spl` / `query_visibility.spl` produce correct results when run
  directly with literal integer args, e.g.
  `bin/simple src/lib/nogc_sync_mut/lsp/lsp_query.spl definition src/lib/common/base_encoding.spl 17 4`
  returns the correct definition list. The corruption happens before the backend is spawned.
- **`protocol.spl::to_int`** — that `to_int(self) -> Int` is a method on the `Severity` enum,
  not on `text`; it cannot match a `text` receiver via UFCS.

## Where it is

In `src/app/simple_lsp_mcp/tools.spl::handle_tool_call` (and `main.spl`), the numeric path:

```
val line0 = line_raw.to_int()          # tools.spl:229
val char0 = char_raw.to_int()          # tools.spl:230
... run_lsp_query(subcmd, file, line0, char0)
# run_lsp_query: [..., str(line0 + 1), str(char0 + 1)]   # tools.spl:15
```

The spawned backend receives a garbage line string. Suspect is the `text → i64` conversion
(`.to_int()`, which resolves via global UFCS to `fn to_int(s: text) -> i64` in
`process_monitor.spl`/`resource_tracker.spl` — NOT imported by `tools.spl`) and/or the numeric
branch of `arg_field` (`tools.spl:157-163`), under native/AOT codegen.

## Why it could not be isolated under interpret

The source path cannot be faithfully reproduced with `bin/simple run`:
`arg_field` / `_find_json_value_start` **diverge between interpret and compiled**. Calling the
exported `handle_tool_call` under interpret returns `"Missing tool name"` because `arg_field`
returns `""` for every field (even `name`) — yet the **compiled** server extracts `name` and
`file` correctly (symbols/completion work). `arg_field` already carries a comment that it was
rewritten to "avoid the Cranelift `match Some(i)` codegen bug", so this module is known to be
codegen-sensitive. Net: the bug is codegen-specific and the interpret path fails earlier at a
different point, so interpret is not a usable repro harness here.

## Proposed next steps

1. Add explicit `to_int(text)->i64` import to `tools.spl`/`main.spl` so UFCS cannot mis-resolve,
   then **rebuild + redeploy** the server and re-run the live tool matrix above.
2. If still broken, instrument `run_lsp_query` to log the exact spawned argv and confirm whether
   `str(line0+1)` or `line_raw.to_int()` is the corruption point.
3. Consider routing position tools through the same backend path as the working string tools, or
   passing the raw `line`/`character` strings through untouched and incrementing inside the
   interpreted backend (no `text↔i64` round-trip in the compiled server).

## Verification harness

```
# string tools (work):
mcp lsp_symbols src/lib/common/base_encoding.spl
# integer tools (broken): lsp_definition @ line 16, char 3 → garbage line_num
# backend sanity (works):
bin/simple src/lib/nogc_sync_mut/lsp/lsp_query.spl definition src/lib/common/base_encoding.spl 17 4
```
