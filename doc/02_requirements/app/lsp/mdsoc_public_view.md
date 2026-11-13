# MDSOC+ Public View by Feature and by Layer — Requirements

**Feature:** MDSOC+ public view (LSP, lsp-mcp bridge, MCP `source_open`)
**Status:** Draft
**Design:** `doc/05_design/app/source_view/public_view_by_feature_layer.md`

## Functional Requirements

- REQ-PUBVIEW-001: Every symbol listing (documentSymbol, workspace/symbol, `lsp_symbols`, `source_open` outline) shall default to the `public` visibility class for files under an MDSOC `__init__.spl` boundary, and shall state the effective default in the response.
- REQ-PUBVIEW-002: Symbols shall be classified as exactly one of `public`, `feature_private`, `layer_private`, `module_private` from the language's visibility rules (`pub`, `pub(peer|up|package|friend)`, layer `__init__.spl` exports, feature capsule exports/expose ports).
- REQ-PUBVIEW-003: The `visibility` argument shall accept `public`, `feature_private`, `layer_private`, `all`, each level adding exactly one further class.
- REQ-PUBVIEW-004: Any response that hides at least one symbol shall carry, in-band in the result body the client reads, a hidden summary with counts by class, counts by kind, the top names, and an exact reveal handle for both MCP tool arguments and raw LSP.
- REQ-PUBVIEW-005: The hidden-summary counts shall equal the number of additional symbols the corresponding reveal level returns.
- REQ-PUBVIEW-006: `source_open` shall record one omission-ledger row (`reason: visibility_hidden`, class, `reopen.visibility`) per hidden top-level node; nothing is hidden without a ledger row.
- REQ-PUBVIEW-007: Workspace views shall support `feature=<capsule id>` (one feature across all its layers) and `layer=<layer dir>` (one layer across all features), and a global view with neither.
- REQ-PUBVIEW-008: The raw LSP shall accept the level through `initializationOptions.simple.visibility` and `workspace/executeCommand simple.setVisibility`, and shall answer hover on a non-symbol position and `simple/hiddenSummary` with the file's hidden summary.
- REQ-PUBVIEW-009: The `simple-lsp-mcp` bridge shall forward `visibility`, `feature`, `layer` tool arguments and the hint text shall name those arguments verbatim.
- REQ-PUBVIEW-010: The LSP and MCP session shall hold one view (`public` default, `feature_private`, `layer_private`, `all`, optional `feature`/`layer` scope) as an immutable value replaced per request; every symbol response states the view it was produced under in the same response shape for every view.
- REQ-PUBVIEW-011: A private session view shall revert to public after N served requests (config `SIMPLE_VISIBILITY_AUTO_REVERT`, default 3) or on an explicit `visibility=public`, and the next response shall state that the view reverted and why.
- REQ-PUBVIEW-012: The view shall be switchable through MCP `simple_set_visibility` and LSP `workspace/executeCommand simple.setVisibility`; a per-request `visibility`/`simpleVisibility` serves that request only and leaves session state unchanged.
