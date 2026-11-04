# Closure-driven refactoring on the shared source-edit core

Status: design + first implementation (2026-11-04). Governs `simple fix`,
`simple code refactor|ast`, LSP `textDocument/codeAction` + `simple/refactor/closure`
+ `simple/ast/views`, and the LSP-MCP bridge tools. Decisions it implements:
EDIT-01..03, MIG-01, ERR-01 (absence is `nil`, never `None`), rev-3 §8-§14, §17.

## 1. Inventory of today's fix paths (what the core replaces, not wraps)

| Path | Edit type | Producer finds site by | Apply | Validation |
|---|---|---|---|---|
| `std.tooling.easy_fix.types` | `Replacement{file,start,end,line,column,new_text}` (byte offsets), `EasyFix{id,description,replacements,confidence}`, `FixReport` | — | `FixApplicator.apply` (sort desc, overlap check, `easyfix_apply_sorted_replacements`) | overlap only; never re-parsed |
| `compiler.tools.fix.rules.registry.check_all_rules_with_lines` | `EasyFix` | 24 hand-listed `check_*` text scanners over `lines` / `LineContext` / `EasyFixSourceView` | — | — |
| `compiler.tools.fix.main` (`simple fix`) | `EasyFix` | `collect_fixes_from_source` = registry + primitive_api + simple_script + todo_format | `apply_fixes_to_disk`: drift guard ("source changed since analysis"), `file_atomic_write` | `source_edits.validated_fix_sources`: bounds, line/col consistency, overlap, same insertion point |
| lint `--fix` (`_LintMain`, `LintDiag.with_easy_fix`) | `EasyFix` | lint checks | same `validated_fix_sources` | same |
| LSP `textDocument/codeAction` -> `src/app/cli/query.spl code-actions` -> `query_commands.query_code_actions` | `EasyFix` -> `{range,newText}` JSON | `check_file` errors + `collect_fixes_from_source` | editor applies | none (editor) |
| MCP `simple_fix` (`main_dispatch.spl:285`) | CLI text passthrough | — | the CLI | the CLI |
| `src/app/spipe/refactor/rewrite.spl` `RewriteEdit` | parallel byte-offset engine | spipe scan | `apply_edits_to_text` | own overlap check — **follow-up: fold into `Replacement`/`validated_fix_sources` (tracked in todo, not this PR)** |

Facts that shape the core: offsets are already byte offsets everywhere; the only
validator is `validated_fix_sources`; the only applier is `FixToolApplicator` +
`apply_fixes_to_disk`; the only producer registry is a hand-written call list.

## 2. One shared core (rev-3 pipeline: snapshot -> producers -> proposal -> staged validation -> apply -> reanalysis)

Pure schemas live in `std.tooling.easy_fix.*`; anything that needs the parser or
a process lives in `compiler.tools.fix.*`. No second edit type, no adapter layer:

| rev-3 schema | implementation |
|---|---|
| `SourceSnapshot` | `easy_fix.snapshot.SourceSnapshot{file, version (sha256 of content), source}` |
| `AstNodeRef` (snapshot-bound) | `easy_fix.node_view.NodeView{file, version, kind, start, end, line, col, ...}` |
| `SymbolRef` | `NodeView.name/owner/module_path/callee`; typed resolution is **verification-pending on stage3** (seed fallback = syntax_only) |
| `Diagnostic` (stable code) | `EasyFix.id = "<CODE>:<file-free suffix>:<line>"`; `easyfix_code(fix)` returns the stable code |
| `EditProposal` | `EasyFix` itself, now carrying `base_version` (snapshot it was computed against) |
| `ValidationReport` | `easy_fix.snapshot.ValidationReport{ok, stage, errors}` from `compiler.tools.fix.source_edits.validate_fix_proposals` |
| `ApplyResult` | `FixReport` + `receipts` (`file old_version -> new_version`) |

### Exposed for matching (`NodeView`)
kind in `fn_decl | class_decl | call | method_call | index | ident | nil_lit | return | unsafe_block`;
`name` (fn/method/ident), `owner` (enclosing class for desugared `Owner__method`),
`owner_type_params`, `params`, `ret_type` (declared return type TEXT, `""` if untyped),
`receiver` (source text), `args_text`, `callee`, `text` (exact node source),
`start/end/line/col`, `header_end` (offset of the `:` that closes a fn header),
`name_start/name_end`, `args_start/args_end`, `stmt_start`, `indent`,
`in_unsafe`, `parent_kind`, `module_path`. Built by
`compiler.tools.fix.node_view_walk.collect_node_views(file, source)` over the pure
Simple parser (`parse_module_silent_checked`, `flat_*_child_*`, byte-offset spans).

### Producers (built-ins and user closures are the same thing)
`FixProducer{code, needs_views}` is plain data; `run_builtin_producer(code, unit)`
(`compiler.tools.fix.builtins`) and `run_registry_producer(code, unit)`
(`rules/registry.spl`) dispatch by code explicitly, so `--diagnostic=CODE`, profiling
labels and the code->rule map are greppable in one place. `FixUnit` = snapshot +
`lines/contexts/std_view` (computed once per file, as before) + `views` (only when a
producer asks). `builtin_fix_producers()` is the registry keyed by diagnostic code
(the 23 former `check_all_rules` rows, `L:primitive_api`, `L:simple_script_required`,
`L:todo_format`, and the bounds slice `PANIC-W-INDEX`). A producer only RETURNS
proposals; it never writes, never validates itself (no self-certification).
Lint `--fix` (`_LintMain.lint_checks`) calls `run_registry_producers(unit)`; the
hand-written `check_all_rules` call list is gone.

A user closure is `FixProducer{code: "R:<name>", run: closure_runner}`:

```
# pure-function shape                      # class shape
fn matches(node: NodeView) -> bool: ...      class FirstToOptional:
fn rewrite(node: NodeView,                     fn matches(node: NodeView) -> bool: ...
           ctx: RewriteCtx) -> [Edit]: ...     fn rewrite(node: NodeView, ctx: RewriteCtx) -> [Edit]: ...
```
`RewriteCtx` helpers (all return `Edit` values, never touch disk): `replace(node, text)`,
`replace_span(node, start, end, text)`, `insert_before/after(node, text)`,
`rename(node, new_name)` (expanded by the engine to every same-name decl/call/ident
in scope), `set_return_type(node, "T?")`, `replace_args(node, text)`,
`reorder_args(node, [i..])` (hoists non-trivial args into `val __tN` temporaries before
the statement so evaluation order is preserved), `note(node, msg)`.

### Sandbox
The closure runs in a child `bin/simple` process (`SIMPLE_EXECUTION_MODE=interpret`)
from a generated harness whose only inputs are hex-embedded `NodeView` records and
whose only output is `@edit|...` lines on stdout. Admission rejects closure text that
contains `use`/`import`/`extern`/`unsafe`/`danger`/`rt_` (no fs, net or FFI reachable);
the run is bounded by `process_run_bounded(timeout_ms, max_output_bytes)`; truncated
output is an error. Memory cap: host-level only — **verification-pending**: in-process
interpreter embedding with a capability-denied extern table needs the stage3 binary.

### Lifecycle (every caller)
1. `fix_snapshot(path)` -> SourceSnapshot (version = sha256).
2. `run_fix_producers(producers, unit)` -> proposals (untrusted).
3. `validate_fix_proposals(proposals, snapshots)` — staged, fail-closed:
   `version` (proposal.base_version == snapshot) -> `edits` (`validated_fix_sources`:
   bounds, coords, overlap/shared insertion point) -> `reparse` (every changed file
   must parse; optional re-typecheck is stage3-pending). Returns `ValidationReport`
   + new sources.
4. Preview: `unified_diff` per file (CLI default) / WorkspaceEdit JSON (LSP, MCP).
5. `apply_fixes_to_disk` (snapshot writer): re-checks disk == snapshot before any
   write and before each atomic write, records receipts. The editor owns unsaved
   buffers, so LSP returns the WorkspaceEdit and never writes.
6. Reanalysis: `fix_reanalyze(files, producers)` re-runs producers on the written
   files and reports the remaining proposal count.

## 3. Surfaces
- CLI `simple fix <file> [--dry-run] [--preview] [--diagnostic=CODE] [--fix-all] [--fix-id=P]`
  — existing lines byte-identical; `--preview` adds the diff; `--diagnostic` filters by code.
- CLI `simple code refactor --closure <file|-> [--scope <glob>...] [--apply] [--json]`
  (dry-run diff by default), `simple code ast <file>` (NodeView JSON).
- LSP `simple/refactor/closure` `{closure, scope: [glob], dryRun}` -> `{workspaceEdit,
  summary:[{file, edits, notes}], validation}`; `simple/ast/views` `{uri}`.
  Standard `textDocument/codeAction` keeps its shape and now comes from the registry.
- LSP-MCP bridge tools `lsp_refactor_closure`, `lsp_ast_views` (child-process, same CLI).

## 4. Example closures (fixtures under `test/fixtures/refactor/`)
- `first_to_optional.spl`: `fn_decl` named `first|last|get|pop` with empty `ret_type`
  -> `set_return_type(node, "<elem>?")` where elem = owner type param; keep `nil`.
- `unchecked_index.spl`: `index` node with `in_unsafe` -> `replace(node,
  "{receiver}.get_unchecked({index})")`; outside `unsafe:` -> `note` (autofix never
  inserts `unsafe`).
- `collections_rename.spl`: `method_call` named `insert` on a map receiver ->
  `rename(node, "set")` with call sites updated (MIG-01: no alias left).

## 5. Open / pending
- Typed receiver/callee resolution (`resolved` vs `syntax_only`) — stage3-pending.
- `PANIC-W-UNWRAP` / `PANIC-W-DIV` producers (lint rule landed in #6526/#6531/#6534, codes
  stable): their fix-it texts carry a `<default>` placeholder, which the reparse stage
  rightly refuses, so they need a *template* proposal kind that previews but is never
  machine-applied (rev-3 "fix-all excludes fallback changes"). `PANIC-W-INDEX` is
  registered now and, per ADR-006, proposes inside `unsafe:` too and never inserts it.
- `simple code ...` dispatch through the pure-Simple registry needs the self-hosted
  CLI (stage3-pending); on the seed invoke `bin/simple src/app/cli/code_entry.spl code ...`,
  which is exactly what the LSP and MCP bridge do.
- `spipe/refactor/rewrite.spl` fold-in — TODO comment at the top of that file
  (picked up by `bin/simple todo-scan`); no bridge was added, the parallel engine is
  simply still there until that step lands.
- Seed interpreter has no `array.sort_by` (`doc/08_tracking/bug/seed_interpreter_array_sort_by_missing_2026-11-04.md`);
  the duplicate-typed-args rule now sorts explicitly.
- Seed interpreter bug: list comprehensions return `[]` under `bin/simple run` (engine
  demoted to hybrid-interp-splice); `SIMPLE_EXECUTION_MODE=interpret` works. Tracked in
  `doc/08_tracking/bug/seed_run_comprehension_empty_hybrid_splice_2026-11-04.md`.
