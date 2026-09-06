# SAML IDE integration

How an editor (VS Code, or the in-repo Simple IDE) reaches the SAML analysis
slice. There is exactly one renderer — `emit_analysis_report` in
`src/lib/common/saml/emit.spl` — so the CLI, the MCP tool, the hover card and
the side panel cannot drift apart.

## Surfaces

| Surface | Entry point | Works today? |
|---|---|---|
| CLI | `bin/simple run src/app/saml/main.spl <check\|analyze\|generate\|doc> <file.saml>` | yes — but **not** as `bin/simple saml ...`, see "Binary caveat" |
| MCP / LSP | tool `saml_analyze` → `src/app/simple_lsp_mcp/tools.spl` | yes, verified over stdio JSON-RPC |
| Simple IDE | `src/app/ide/saml_analysis.spl` — `ide_saml_diagnostics` / `ide_saml_hover` / `ide_saml_panel` / `ide_saml_manual` / `ide_saml_evidence` | yes, self-probe `checks=5/5` |

### CLI

```
simple saml check    <file.saml> [--specs DIR]         # diagnostics; exit 1 on errors
simple saml analyze  <file.saml> [--specs DIR]         # the analysis report
simple saml generate --target baml|markdown|sdn <file.saml> [--out PATH]
simple saml doc      <file.saml> [--out PATH]          # markdown manual
```

`--specs DIR` (default `test/`, landed 2026-08-10) is walked for
`*_spec.spl` files whose coverage folds into the evidence ladder as
`external:<path>:<it_title>` entries — see "Report shape" below and
`doc/07_guide/infra/llm/saml_guide.md` for the full match rule.

Exit codes: `0` ok, `1` failure (unreadable input, error-severity SAML
diagnostics, write failure), `2` usage error. `check` prints one
`path:line: severity: code: message` per diagnostic, then the analysis
warnings, then a `check: <path> errors=N warnings=M` summary line — that
summary line is the authoritative verdict.

Registered in the dispatch table at `src/app/cli/dispatch/table.spl` under the
name `saml`. Until the pure-Simple binary is rebuilt, the working invocation is
`bin/simple run src/app/saml/main.spl <sub> <file.saml>` — note the `run`
verb; without it the seed reports `file not found` (see "Binary caveat").

### Simple IDE

`src/app/ide/saml_analysis.spl` exposes the same analysis in the three shapes
an editor consumes, and is registered as a row in `ide_feature_check_report`:

| Function | Returns | Editor use |
|---|---|---|
| `ide_saml_diagnostics(source, path)` | `["<line>:<severity>:<message>", …]` | inline squiggles — split on the first two colons, no parser needed |
| `ide_saml_hover(source, path, fn_name)` | lines for one function | hover card |
| `ide_saml_panel(source, path)` | the whole report, split into lines | side panel |
| `ide_saml_manual(source, path)` | Markdown | preview pane |
| `ide_saml_evidence(source, path, spec_paths, spec_sources)` | the whole report (via `analyze_module_with_specs` + shared `emit_analysis_report`) | same as `ide_saml_panel` but with external `test/**/*_spec.spl` coverage folded in; landed 2026-08-10, pushed the self-probe from `checks=4/4` to `checks=5/5` |

## `saml_analyze` MCP tool

Advertised by `lsp_tools_list_result` in `src/app/simple_lsp_mcp/main.spl`
alongside the eleven `lsp_*` tools, and dispatched by `handle_tool_call` in
`src/app/simple_lsp_mcp/tools.spl`.

Request:

```json
{"jsonrpc":"2.0","id":3,"method":"tools/call",
 "params":{"name":"saml_analyze","arguments":{"file":"/abs/path/support.saml"}}}
```

`file` is required; an empty or missing `file` returns a tool error
`Missing required argument: file`.

An optional `spec_dir` argument (landed 2026-08-10) folds in coverage from
`test/**/*_spec.spl` files under that directory, forwarded to the CLI as
`--specs <spec_dir>`:

```json
{"jsonrpc":"2.0","id":4,"method":"tools/call",
 "params":{"name":"saml_analyze",
   "arguments":{"file":"/abs/path/support.saml","spec_dir":"test/"}}}
```

Omitted or empty `spec_dir` falls back to the CLI's own default (`test/`),
never errors (`src/app/simple_lsp_mcp/tools.spl:run_saml_analyze`).

Response — a standard MCP tool result whose single text block is the verbatim
`emit_analysis_report` output:

```json
{"jsonrpc":"2.0","id":3,"result":{"content":[{"type":"text","text":"SAML ANALYSIS ...\n..."}]}}
```

Unlike `lsp_diagnostics`, this tool spawns a plain script rather than the
`simple check` CLI subcommand, so it is not affected by the source-mode
`process_run` deadlock and needs no `SIMPLE_LSP_ENABLE_DIAGNOSTICS` gate.
Measured cost: 0.51 s cold for a 36-line module, well inside the server's
10 s command timeout.

## Report shape the client parses

```
SAML ANALYSIS <source_path>
module=<name> functions=<n> errors=<n> warnings=<n>

fn <signature>  [line <N>]
  client:     <client>
  schema:     <Type, Type, ...>
  prompt:     vars=<a,b> output_format=<bool>
  parse:      strictness=<s> traced=<bool>
  evidence:   <state> tests=[<t,...>] examples=<n> counter=<n>
              # each entry in tests=[...] is either an in-file test-block
              # name, or (landed 2026-08-10, when --specs/spec_dir supplied
              # a match) "external:<path>:<it_title>" naming the sspec
              # file and `it "..."` title that covers the function.
              # External coverage lifts unevidenced -> tested, never -> red_proven.
  sensitive:  <Type.field ("tag"), ...>        # omitted when empty
  ! <warning>                                  # zero or more, per function
! <module warning>                             # zero or more, module level
```

Three stable anchors do all the work for a client: the `module=` header line,
each `fn ... [line N]` block header (which carries the line number to attach
to), and the `!`-prefixed warning lines.

## Rendering guidance

**Inline diagnostics.** Attach each `  ! ...` line to the line number in its
enclosing `fn ... [line N]` header; attach each top-level `! ...` line to line
1. Severity: DiagnosticSeverity.Warning, source `saml`, code = the leading
`E-SAML-NNNN` token when present. For a save-time hard gate use the CLI
(`simple saml check`) instead and read its exit code — `saml_analyze` never
fails, it reports.

**Hover card.** On hover over an `llm fn` name, find the block whose header
matches that name and render the block body as a fenced code block or a small
key/value table. The evidence line is the one worth styling: `red_proven` /
`tested` / `examples_only` / `unevidenced`, badged in that order of strength.
Show the `sensitive:` row prominently when present — it is a policy signal, not
trivia.

**Side panel.** Drive a per-module tree view from the header line: module name,
function count, error/warning counts as a status bar, then one collapsible node
per function labelled `name — evidence_state (W warnings)`. Clicking a node
reveals to `[line N]`. Refresh the panel on document save; a full re-analysis is
sub-second, so incremental invalidation is unnecessary.

**Generated projections.** Wire `generate --target baml|markdown|sdn` to editor
commands ("SAML: Export BAML" etc.) writing via `--out`; they are ordinary
stdout/file emitters and need no LSP plumbing.

## Binary caveat

`bin/simple` is currently the Rust bootstrap **seed**. Its argv parser is Rust
and never consults `src/app/cli/dispatch/table.spl`, so `bin/simple saml ...`
prints `error: file not found: saml`. The table entry takes effect only for the
pure-Simple binary. The MCP server is unaffected because `.mcp.json` launches
it in source mode (`bin/simple run src/app/simple_lsp_mcp/main.spl`), which
does pick up the new tool immediately.
