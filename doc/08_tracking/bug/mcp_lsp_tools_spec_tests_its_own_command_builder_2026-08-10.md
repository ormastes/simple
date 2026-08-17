## Re-verified 2026-08-17 — STILL OPEN, unchanged

`test/01_unit/app/mcp_unit/mcp_lsp_tools_spec.spl` still builds the shell command
inside the spec (58 `timeout 30 bin/simple` string constructions) and imports the
product **zero** times (`grep -c "use std\|use app"` = 0). The spec remains
vacuously green: it cannot fail if the handlers in
`src/lib/nogc_async_mut/mcp/main_lazy_query_tools.spl` are wrong or absent.

# `mcp_lsp_tools_spec` tests its own command builder; product has no testable seam

- **Status:** OPEN (spec is vacuously GREEN — 78/78 — and proves nothing)
- **Filed:** 2026-08-10 (stream P2)
- **Files:** `test/01_unit/app/mcp_unit/mcp_lsp_tools_spec.spl`,
  `test/unit/app/mcp_unit/mcp_lsp_tools_spec.spl` (identical mirrors)
- **Product:** `src/lib/nogc_async_mut/mcp/main_lazy_query_tools.spl:612-800`

## Defect

All 78 examples build the shell command **inside the spec file** and then assert
against their own construction, e.g.

```
val file = "src/app/cli/main.spl"
var cmd = "timeout 30 bin/simple query signature-help " + file + " " + line
expect(cmd).to_contain("signature-help")
```

The product is never read or called. The spec is green whether the handlers are
correct, wrong, or absent. It covers ten tools (`simple_signature_help`,
`simple_rename`, `simple_code_actions`, `simple_workspace_symbols`,
`simple_call_hierarchy`, `simple_type_hierarchy`, `simple_semantic_tokens`,
`simple_inlay_hints`, `simple_selection_range`, `simple_document_formatting`).

Current verdict, both trees:
`declared>=78 executed=78 passed=78 failed=0 dropped=0`.

## Why it was not rewritten in this pass

The sibling spec `mcp_analysis_tools_spec` was rewritten to call the real
handlers, which works because those handlers return structured text from cheap
in-process work or a single grep. The LSP handlers are different: each one is
`extract_field(...)` + argument validation + **`shell_cmd("timeout 30 " + binary
+ " query <sub> ...")`**. There is no seam between building the command and
running it. Calling the ten handlers 78 times would spawn 78 subprocesses of up
to 30s each — unacceptable for a unit spec — and would still not check the flag
ordering that is the spec's actual subject (e.g. `column` must be appended
*before* `--new-name` in `handle_simple_rename`, line 628-643).

## Required product change (the unblock condition)

Extract the command construction from each handler into a pure builder, e.g.

```
fn _lsp_query_cmd(sub: text, file: text, line: text, column: text, extra: [text]) -> text
```

so the handler becomes `shell_cmd(_lsp_query_cmd(...))`. The spec then asserts
on `_lsp_query_cmd` output — real product code, no subprocess. Do this for all
ten tools; the error-path examples (`Missing required parameter: ...`) can call
the real handlers directly today, since those return before `shell_cmd`.

Until that seam exists, the spec cannot be rewritten without either fabricating
the logic again or making a unit spec spawn 78 subprocesses.

## Related measurement trap found while verifying

Sabotaging `src/app/mcp/main_lazy_query_tools.spl` **and**
`src/lib/nogc_async_mut/mcp/main_lazy_query_tools.spl` (the only two files in
the tree containing the literal `-- simple_search query=`) left
`mcp_analysis_tools_spec` at 37/37 PASS under `bin/simple test`, including with
`--clean`. The assertions are provably live — an impossible-token probe against
the same handler goes RED — so `use app.mcp.*` under the test runner appears to
bind to a **cached/embedded copy** of the app module rather than the working-tree
source. Sabotage-proof of `src/app/**` code via `bin/simple test` is therefore
unreliable; this does not apply to `src/lib/**` (the `std.service` sabotage in
`service_lease_manager_and_request_queue_are_value_type_no_ops_2026-08-10.md`
did land). Worth a separate investigation.
