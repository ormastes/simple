# TRACE32 MCP module owner omissions

Status: permanent source repairs prepared; native validation pending.

Early Phase4 with producer `2b831559` and immutable source `916be6` completed HIR
with 2,583 successes and nine failed modules. Six failures are the MCP TRACE32
tool families. Evidence: `early-p4-full-cli-916be/hir-failure-diagnostics.json`.
The other three editor/browser modules have a separate repair owner.

The physical Git owners are under
`examples/10_tooling/trace32_tools/t32_mcp`; `src/app/mcp_t32` is their declared
source alias. The module split omitted lexical imports for existing JSON,
session, and state helpers. The ctypes bridge omitted the existing session
type. Session tools called an undeclared raw environment getter despite already
importing the environment facade. The window action reader assigned an
undeclared local. These are source defects, not established compiler defects.

Repairs name the existing owners, use the environment facade's established
empty-on-absent behavior, and declare the parsed action array. Session-ID
collection has one small shared owner with compatibility re-exports, avoiding
a session-tools to action-dispatch dependency cycle. Existing JSON error
messages are retained; five job branches now supply the required numeric error
argument (invalid job identifier -32602; operation state/failure -32000).

Ten standalone checks cover actual JSON escaping, empty session inventory,
unloaded ctypes availability, missing-name/session errors, rejected headless
setup without state mutation, and action-catalog contents. All ten are UNRUN.
They use a fresh process and do not connect to TRACE32 or spawn a backend.

These imports/declarations must remain after future compiler rebuilds. They are
not temporary compiler workarounds and must not be automatically reverted.
The failed original Phase4 receipts and cache are retained; the next attempt
uses the current compiler and a separately authenticated source revision.
