# Legacy MCP feature tests target a REMOVED API and assert nothing

Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 02).
**Found:** 2026-08-04
**Severity:** medium · **Area:** legacy feature suite / MCP server
**Found during:** legacy-feature-test triage (`test/03_system/feature/lib/mcp`)

## Symptom

`test/03_system/feature/lib` reports 9 failures out of 81; 7 of them are the
MCP smoke tests, all with the same runner verdict:

```
$ SIMPLE_TIMEOUT_SECONDS=0 bin/simple test test/03_system/feature/lib --no-cache --no-cover-check
FAIL test/03_system/feature/lib/mcp/bootstrap_import_test.spl (0 passed, 1 failed)
     Error: no parseable pass/fail summary in test output; refusing synthetic pass
FAIL test/03_system/feature/lib/mcp/bootstrap_e2e_test.spl (0 passed, 1 failed)
     Error: semantic: Cannot resolve module: app.mcp.session
```

Actual: no assertions run; the runner refuses to synthesise a pass.
Expected: either a real pass/fail verdict, or the file is not a test.

## Root cause

Two compounding facts, both verified on 2026-08-04.

**1. The API these tests exercise no longer exists.** Symbol search over
`src/app/mcp/` and `src/lib/nogc_sync_mut/mcp/` (26 modules):

| symbol imported by the tests | present in src today |
|------------------------------|----------------------|
| `McpState` (`app.mcp.session` / `std.mcp.session`) | **MISSING** — no `session` module, no `McpState` anywhere |
| `init_core_schemas` | **MISSING** |
| `get_all_tool_schemas` | **MISSING** |
| `extract_json_string_v2` | **MISSING** |
| `extract_arguments_dict` | **MISSING** |
| `jo3` | present (`src/app/mcp/api_tools.spl`) |
| `extract_nested_string` | present (`src/app/mcp/api_tools.spl`) |

The live MCP server is `src/app/mcp/main.spl` + `main_dispatch*.spl` +
`main_lazy_*.spl`; it was restructured away from the `session`/`schema` shape
these tests were written against. **The tests are the stale side.**

**2. They could never have caught the removal, because they assert nothing.**
Every one of them is a print-only `fn main()` smoke script — e.g.
`test/03_system/feature/lib/mcp/bootstrap_import_test.spl`:

```simple
fn main():
    init_core_schemas()
    print("✓ init_core_schemas works")
    ...
main()
```

`✗` branches only *print*; there is no `expect`, no `assert_*`, and no non-zero
exit. Combined with the known "an unresolved `use` is only a WARN" behaviour,
these files stayed green for as long as the runner accepted a zero exit code.
The current runner refusing a synthetic pass is the *correct* behaviour and is
what finally surfaced the rot.

Affected files (identical pairs exist in the legacy `test/feature/` mirror):

- `test/03_system/feature/lib/mcp/bootstrap_e2e_test.spl`
- `test/03_system/feature/lib/mcp/bootstrap_functions_test.spl`
- `test/03_system/feature/lib/mcp/bootstrap_import_test.spl`
- `test/03_system/feature/lib/mcp/bootstrap_protocol_test.spl`
- `test/03_system/feature/lib/mcp/bootstrap_protocol_simple.spl`
- `test/03_system/feature/lib/mcp/handler_import_test.spl`
- `test/03_system/feature/lib/mcp/lazy_loading_v2_test.spl`
- `test/03_system/feature/lib/mcp/schema_simple_test.spl`
- `test/03_system/feature/lib/mcp/simple_import_test.spl`
- `test/03_system/feature/lib/mcp/working_check.spl`
- `test/03_system/feature/lib/mcp/working_check_direct.spl`
- plus the same 11 under `test/feature/lib/mcp/`

(A repo-wide scan for the same shape — `fn main` with no `expect(`/`assert_`/
`describe `/`it "` — finds 27 files in the legacy feature trees; 22 of them are
these MCP pairs.)

## Why not fixed now

The honest repair is to rewrite each file as an SSpec against the *current*
`src/app/mcp` entry points, which means first deciding what the intended
contract of the restructured server is (there is no `session` concept left to
port `McpState` onto). That is MCP-owner work, not a mechanical rename, and
guessing an equivalent would fabricate coverage. Deleting them is also wrong on
its own: the *intent* they encode (bootstrap imports resolve, schemas
initialise, the JSON helpers round-trip) is still worth asserting — it just has
to be re-pointed at the live API.

## 2026-08-09 re-verification (worktree agent)

Re-checked the symbol-removal claim fresh: `/usr/bin/grep -rl "McpState"
src/app/mcp src/lib/nogc_sync_mut/mcp` and the same for `init_core_schemas`
both return zero hits in this worktree — confirms neither symbol exists
anywhere under the current MCP source tree, matching the doc's table exactly.
The live MCP server (`src/app/mcp/main.spl` + `main_dispatch*.spl` +
`main_lazy_*.spl`) has no `session`/`McpState` shape to port these tests onto,
so a same-session rewrite would be a guess, not a verified equivalent —
exactly the fabrication risk the doc already flags. **Confirmed
ARCHITECTURAL-OPEN**: this needs an MCP-owner decision on the restructured
server's intended contract before the 22 stale smoke tests can be rewritten as
real assertions; no mechanical fix is safely in scope here. Left OPEN with
this fresh confirmation; no code change made.

## Triage 2026-08-17 — REPRODUCED LIVE (content evidence), now FIXED

Classified against current source, not SHA ancestry.

Two claims, one stale and one live:

1. STALE: the doc says the file imports a removed `api_tools` API.
   `grep api_tools test/03_system/feature/lib/mcp/bootstrap_e2e_test.spl` returns
   nothing, and `src/app/mcp/api_tools.spl` still exists. The removed import was
   actually `use app.mcp.session.{McpState}` — `src/app/mcp/session.spl` is
   absent and `McpState` is defined nowhere under `src/app/mcp/` (only
   `assistant/session_*.spl` files exist, none defining it).

2. LIVE: "asserts nothing" was exactly right. The file was a plain `fn main()`
   whose every check was `if ok: print("✓") else: print("✗")`. The failure branch
   printed and the process still exited 0 with no `Results:` line, so a
   regression was indistinguishable from a pass. This is the silent-green class.

Fix: converted to `describe`/`it` with real `expect`/`assert_true` oracles,
mirroring the conversion already landed in
`test/feature/lib/mcp/bootstrap_protocol_test.spl`. The unresolvable
`app.mcp.session.McpState` import and its "McpState creation works" check were
dropped rather than faked; recorded here so the loss of that coverage is not
silent. Restoring it needs whoever removed `McpState` to say where it went.

Similar-bug-class detection spec added:
`test/03_system/feature/lib/mcp/vacuous_print_only_test_detection_spec.spl` —
fails if ANY `*_test.spl`/`*_spec.spl` in the two MCP feature trees contains no
oracle token, with a positive control so a scan that scanned nothing cannot pass.

## Re-triage 2026-08-17 (content-classified, m9a_tests lane)

**Verdict: ALREADY FIXED — both halves of the title are false today.**

*"imports a removed api_tools API"* — `test/03_system/feature/lib/mcp/bootstrap_e2e_test.spl`
imports only two modules, and both resolve:

- line 14: `use std.mcp.helpers.{LB, RB, jp, js, jo3, extract_json_string_v2, extract_json_value, extract_nested_string, make_error_response, make_result_response}` -> `src/lib/nogc_async_mut/mcp/helpers.spl`
- line 15: `use std.mcp.schema.{get_all_tool_schemas, init_core_schemas}` -> `src/lib/nogc_async_mut/mcp/schema.spl`

The file even carries its own repair note at line 8: *"Also dropped `use
app.mcp.session.{McpState}`: that module does not exist"*. There is no
`api_tools` import left to be stale.

*"assert nothing (vacuous green)"* — the file is 50 lines with **six** `it`
blocks, each carrying a real assertion, none of them trivially true:

- line 22 `expect(schemas.len()).to_be_greater_than(100)`
- line 26 `expect(extract_json_string_v2(test_json, "method")).to_equal("initialize")`
- line 34 `expect(extract_nested_string(test_json, "params", "protocolVersion")).to_equal("2024-11-05")`
- plus raw-value extraction (28), three-field response construction (36), error-code response (42), tools/call content-block response (47)

Recommend closing. (Not runtime-confirmed from this lane — see the parent
reports Unproven list — but the two specific defects the doc names are
verifiably absent from current content.)
