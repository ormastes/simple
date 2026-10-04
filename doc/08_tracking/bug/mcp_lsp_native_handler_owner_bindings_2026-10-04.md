# Native MCP/LSP handler owner bindings

Source baseline: `f6026d340a59de8a35389eba53f540d1d5c155a9`.

The retained Windows Phase4 MCP and LSP diagnostics identify missing JSON
helpers, the binary locator, and session validation helpers in independently
compiled handler modules. Bind each name to its existing declaration owner.
Keep binary location and hardware validation imports inside their existing
handler paths so the repair does not eagerly load their dependency trees.

The dialog caller also used `allowed_types` although `_require_hw_session`
declares `required_types`. Correct that argument instead of adding a second
validator or accepting an ignored argument.

The other reported symbols in `main_dispatch`, `main_lazy_protocol`, and the
LSP local handlers already have function-local imports. Their compiler
local-use preservation repair is present in this baseline; its refreshed
producer validation is separate. This patch does not hoist those imports or
claim their native failures have closed.

Regression: `test/01_unit/app/mcp/native_handler_owner_binding_spec.spl`
contains five actual handler-output cases: numeric and quoted LSP request IDs,
notification suppression, missing debug/read arguments, and a nonexistent
hardware session. The latter calls the actual shared validator before any
TRACE32 process launch. No test substitutes a fake JSON helper or handler.

Validation status: native execution is **UNRUN**, pending the refreshed Phase2
producer and the independent product retry. These are five registered source
cases, not five executed or passing cases. Retained evidence is
`runtime/windows-restart-20261004/phase4-failure-groups/{mcp,lsp}-diagnostics.json`
under the external session packet; no frozen source or cache was modified.
