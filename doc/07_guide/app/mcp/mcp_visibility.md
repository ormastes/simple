# MCP/LSP MDSOC Visibility Tools — Guide

Design: `doc/05_design/app/mcp/mdsoc_visibility_requester_design.md`.

## What you get

For a **requester location** (`path[:line]`), two compact sets for a target
file — each entry `{symbol, kind, module|feature, why}`:

- **layerPublic** — symbols that cross their MDSOC layer boundary (nearest
  `__init__.spl`; `pub` + `export`-line re-export ⇒ public, `pub` inside the
  boundary ⇒ visible to a requester sharing that boundary/package/friend).
- **featurePublic** — symbols a feature capsule (`arch { dimension =
  "feature" }`, e.g. `src/compiler/85.mdsoc/feature/parsing/`) exports across
  the feature boundary: named in a capsule `export` line, declared non-private
  in an `exports.expose` port path, or re-exported by an exposed port file.

## Requester default = last code read

Omit `requester` and the server uses the last file this session read/opened:
- simple-mcp: `simple_read` / `editor.open_file` / `editor.read_buffer`;
- simple-lsp-mcp: the last position-tool call (`lsp_hover(file, line, …)`).

With nothing read yet the result says `"source":"none"` with an explicit note
and shows only boundary-crossing symbols — it never silently uses the target
file as its own requester.

## Tools

| tool | server | args |
|---|---|---|
| `simple_visibility` | simple-mcp | `file?`, `requester?` (file defaults to the requester's file) |
| `simple_symbols` | simple-mcp | `path`, `requester?` — per-symbol `simpleVisibility` + `featureVisibility` |
| `simple_context` | simple-mcp | `requester?` — appends a `--- Visibility (requester=…) ---` section |
| `lsp_visibility` | simple-lsp-mcp | `file?`, `requester?` |
| `lsp_symbols` | simple-lsp-mcp | `file`, `requester?` |
| `lsp_hover` | simple-lsp-mcp | `file`, `line`, `character`, `requester?` |

CLI equivalent:

```bash
bin/simple run src/app/cli/query_visibility.spl visibility \
  src/compiler/85.mdsoc/feature/lexing/app/ports.spl \
  --requester src/compiler/80.driver/driver.spl:100
```

Example (trimmed):

```json
{"requester":{"file":"src/compiler/80.driver/driver.spl","line":100,"source":"explicit"},
 "target":"src/compiler/85.mdsoc/feature/lexing/app/ports.spl",
 "feature":"compiler.85.mdsoc.feature.lexing",
 "layerPublic":[],
 "featurePublic":[{"symbol":"LexerOutputPort","kind":"reexport",
   "feature":"compiler.85.mdsoc.feature.lexing",
   "why":"named in an export line of a capsule __init__.spl"}]}
```

Specs: `test/01_unit/app/cli/query_visibility_feature_spec.spl`,
`test/01_unit/app/mcp/mcp_visibility_requester_spec.spl`,
`test/01_unit/app/simple_lsp_mcp/lsp_visibility_requester_spec.spl`.
