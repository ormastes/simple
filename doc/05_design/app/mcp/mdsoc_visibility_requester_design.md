# MDSOC Visibility with a Requester Location — Design (2026-08-28)

Requirement: "LSP by MDSOC which shows layer-public and feature-public symbols
based on the last code read or a specified location."

## Requester location

A requester is `path[:line]`. The line is echoed back (visibility is
file-granular today; the line is reserved for declaration-scoped rules).
Resolution order, identical in both servers:

1. **explicit** — the tool call's `requester` argument;
2. **last_read** — per-server-session state:
   - simple-mcp: the last file read/opened via `simple_read`,
     `editor.open_file`, `editor.read_buffer`
     (`src/app/mcp/main_session_state.spl`; in-process, never the
     cross-process `/tmp` editor file);
   - simple-lsp-mcp: the last `file`(+`line`) a POSITION tool
     (`lsp_hover`, `lsp_definition`, …) was called with
     (`src/app/simple_lsp_mcp/session_state.spl`). File-only tools
     (`lsp_symbols`, `lsp_visibility`) never update it, and the requester is
     resolved BEFORE the call records its own position;
3. **none** — no silent fallback to the target file (`--requester <file>
   <file>` was the old bug: every answer was "visible from itself"). The
   result carries `source: "none"` plus an explicit note, and reachability
   degrades to "crosses the boundary from anywhere".

CLI carrier: `src/app/cli/query_visibility.spl visibility [file]
--requester p[:l] --requester-source explicit|last_read|none`, plus
`--requester` on `symbols` and `hover`.

## Layer axis (existing, two fixes)

Unchanged model: nearest ancestor `__init__.spl` = boundary;
`simpleVisibility{display, reachable, boundaryKind, boundaryModule, declared}`.
Fixes:
- `exported_by` now also matches bare `export A, B` manifest lines (before,
  only `export use …` counted, so `lib/nogc_sync_mut/__init__.spl`'s
  `export basename, dirname, …` did not make `basename` layer-public);
- empty requester now means "reachable iff display == public", not
  "reachable: true for everything".

## Feature axis (new)

**Feature capsule** := nearest ancestor directory whose `__init__.spl`
declares `arch { dimension = "feature" … }` — the tree's existing convention
(`src/compiler/85.mdsoc/feature/<name>/`, 12 capsules; MDSOC+ doc
`doc/04_architecture/compiler/mdsoc/mdsoc_architecture_tobe.md` Part 3 keeps
the outer MDSOC boundary and adds ECS inside — the exported port surface IS
the feature boundary). Feature id = capsule dir relative to `src/`, dotted
(`compiler.85.mdsoc.feature.lexing`).

**Feature-public** (symbol S in file F of capsule C) iff any of:
1. S is named in an `export A, B` / `export use m.{A,B}` line of an
   `__init__.spl` between F and C's root;
2. F is under a manifest `exports { expose = ["./app/ports"] }` path and S is
   declared non-private;
3. F is an exposed port file and S is a name it re-exports via `use m.{S}`
   (port files declare nothing themselves).

**Reachability**: feature-public → reachable from anywhere; otherwise only
from a requester inside the same capsule; with no requester, only
feature-public. `imports { deny = [...] }` (virtual-path globs on the
requester's own capsule) is NOT enforced — deliberate scope cut, the import
axis belongs to the arch checker, not symbol visibility.

Implementation: `src/app/cli/_QueryVisibility/feature_visibility.spl` (leaf
module); surfaced as the `featureVisibility{feature, exported, reachable,
why?}` sibling of `simpleVisibility`, omitted outside feature capsules.

## Output shape (`visibility` subcommand / `simple_visibility` / `lsp_visibility`)

```json
{"requester":{"file":"…","line":100,"source":"explicit|last_read|none","note?":"…"},
 "target":"…","layerModule":"compiler.80.driver","feature":"…|",
 "layerPublic":[{"symbol":"…","kind":"fn","module":"…","why":"pub, re-exported by …"}],
 "featurePublic":[{"symbol":"…","kind":"struct|reexport","feature":"…","why":"named in an export line …"}]}
```

## Specs

- `test/01_unit/app/cli/query_visibility_feature_spec.spl` — classification on
  real fixtures (85.mdsoc feature capsules, 80.driver, lib/nogc_sync_mut).
- `test/01_unit/app/mcp/mcp_visibility_requester_spec.spl` — dispatch_tool:
  explicit / default-to-last-read / no-read note / error when neither.
- `test/01_unit/app/simple_lsp_mcp/lsp_visibility_requester_spec.spl` — same
  over handle_tool_call, incl. resolve-before-record.
- E2E stdio transcript: simple-mcp source-run (scratchpad `vis/e2e_mcp.*`).
