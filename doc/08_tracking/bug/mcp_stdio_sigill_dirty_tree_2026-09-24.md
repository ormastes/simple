# simple_lsp_mcp / mcp SIGILL (illegal instruction) at EOF under dirty worktree (2026-09-24)

## Symptom

`bin/simple run src/app/simple_lsp_mcp/main.spl` (and `src/app/mcp/main.spl`, and
`bin/simple check src/app/mcp`, `bin/simple check src/app/simple_lsp_mcp`) exit with
**SIGILL (132, "illegal instruction", core dumped)** on this aarch64 host when stdin
reaches EOF, **in the current dirty worktree**. The JSON-RPC responses themselves are
correct (initialize/tools/list answered before the crash). Minimal `fn main()` probes
do not crash.

## Baseline comparison (same seed binary `bin/release/aarch64-unknown-linux-gnu/simple`)

| tree state | run | result |
|---|---|---|
| HEAD sources (stash of dirty state) | `run src/app/simple_lsp_mcp/main.spl` | exit 0 |
| dirty worktree | `run src/app/simple_lsp_mcp/main.spl` | SIGILL |
| dirty worktree | `run src/app/mcp/main.spl` (no local edits) | SIGILL |
| dirty worktree | `check src/app/mcp` / `check src/app/simple_lsp_mcp` | SIGILL |
| **clean HEAD checkout (temp worktree)** | `check src/lib` | **SIGILL too** |
| dirty worktree | `check src/compiler` / `check src/lib` | SIGILL (crashes seconds in, during load) |

Refinement of the original hypothesis (measured with a clean-HEAD temp worktree):
the wholesale `check src/lib` / `check src/compiler` SIGILL happens **even at clean
HEAD** with the current seed binary — it is NOT caused by the dirty worktree. What IS
dirty-worktree-specific is pulling the duplicate-signature modules into an app `run`
(HEAD runs of simple_lsp_mcp print 0 collision warnings; dirty runs print 8 and then
SIGILL at EOF). So the root family is one: the seed's ambiguous
duplicate-symbol fallback misdispatching (ud2 trap) — the dirty tree enlarges the set
of programs that contain both copies; `check` always compiles both.

## Leading evidence

The dirty-tree runs print 8 x `compiler_cross_module_private_symbol_collision`
warnings: `jo1/jo2/jo3/jo4`, `extract_json_string`, `extract_json_value`,
`make_tool_error`, `_assistant_append_jsonl` each have **two co-compiled definitions
with differing signatures** — `(String)->String` from
`src/lib/nogc_sync_mut/mcp_sdk/core/json.spl` (via `std.mcp_sdk.*`) vs `(text)->text`
from app-local `json_helpers.spl` / `std.mcp.helpers`. HEAD runs print **zero** such
warnings. The lint itself warns: "a fallback hit may still dispatch to the wrong
one" — a misdispatched call is the prime suspect for the SIGILL (ud2 trap).

Dirty files in the MCP import graph at the time of the crash:
`src/app/mcp/{api_tools,bootstrap/main_optimized,debug_handlers,debug_tools,main_lazy_protocol,virtual_summary_protocol}.spl`,
`src/app/simple_lsp_mcp/{json_helpers,tools}.spl`. The new import edge that pulls the
second (String-typed) copy into each program is **not yet identified**;
`virtual_source_read_registry_v1` was checked and is not it.

## Impact

- Blocks the AGENTS.md-mandated gates `bin/simple check src/app/mcp` and
  `bin/simple check src/app/simple_lsp_mcp` (both SIGILL) for any MCP/LSP change
  made in the dirty tree.
- `test/02_integration/app/mcp_stdio_integration_spec.spl` passes;
  `test/02_integration/app/simple_lsp_mcp_stdio_spec.spl` fails 4/4 on this host for
  a **different, environmental reason**: it hardcodes
  `bin/release/linux-x86_64/simple_lsp_mcp_server`, which does not exist on aarch64
  hosts (see companion note in this fix's commit).

## Suggested next steps

1. Bisect the dirty files above (revert each in a scratch worktree) to find the
   import edge that co-compiles `mcp_sdk/core/json.spl` with the local helpers.
2. Alternatively make the seed fail closed (hard error) instead of misdispatching
   when an ambiguous duplicate-symbol fallback is hit — the lint already detects
   the situation; the silent wrong-dispatch is what turns it into SIGILL.
