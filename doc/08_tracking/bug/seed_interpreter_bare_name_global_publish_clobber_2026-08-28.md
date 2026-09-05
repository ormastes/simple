# Seed interpreter: caller local sharing a global's bare name clobbers the global on call-out

**Date:** 2026-08-28  **Status:** worked around in Simple source; seed defect open
**Symptom:** `error: semantic: nil is forbidden by the non-optional return contract of 'decl_get_span'`
while `native-build` parses `src/app/mcp/main_lazy_ctx_tools.spl` (blocks the MCP server rebuild,
`doc/07_guide/app/mcp/mcp.md` path). Reproduce spec:
`test/01_unit/compiler/frontend/module_const_after_fns_span_arena_spec.spl` (fails pre-fix with the
exact production error, passes post-fix).

## Observed (probe sequence, seed sha256 `57b5f990f06df033…`, tree e029b09f55a)

The module-body loop in `enum_module_body.spl` (`parse_module_body`, one frame alive for the whole
file) parsed the ctx-tools file: 10 consts, then 49 fns, then `const _CTX_HOOK_FILES: [text] = [...]`.
Probes on the arena globals in `compiler.core.ast` (`decl_nodes.spl`):

| point | decl_tag.len | decl_span.len |
|---|---|---|
| after decl 68 (`handle_simple_ctx_stats`) | 69 | 69 |
| in the loop frame, right before `decl_val_binding(...)` for decl 69 | 69 | 69 |
| `decl_ensure_slot` pre-loop (inside decl_nodes) | 69 | 69 |
| inside `decl_push_default_slot`, after `decl_tag.push` / `decl_span.push` | 70 | **20** |

20 is exactly the arena length right after decl 19, the last *previous* const parsed by the same
loop frame. `decl_span` reverted to that stale copy; `decl_tag` kept growing; every later decl's
span slot became nil; `decl_get_span(20)` (fn `_ctx_chunks_path`) returned nil in the flat-AST
bridge (`convert_nodes.spl:decl_span_for`) and tripped the seed's return contract.

Renaming the loop frame's local `val decl_span = flat_span_new(...)` to `decl_span_id` removes the
truncation entirely (parse 30/30 files, no mismatch, spec green). Nothing else changed.

## Mechanism (consistent with the seed source, not step-traced in the binary)

`src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs`:
`publish_live_bound_globals` / `refresh_live_bound_globals` / `publish_and_repoint` sync a frame's
overlay entries with `MODULE_GLOBALS`, a store keyed by **bare name**. A local in a long-lived frame
that happens to share the bare name of another module's global (`decl_span`) is treated as a bound
copy of that global: it is refreshed with the live array after the frame's first call into
`decl_nodes` (decl 19), and published back over the live global on the frame's next call-out into
that module (decl 69). Short-lived frames (`parse_fn_decl`, `parse_module_decl_with_visibility`)
also had a `decl_span` local but return before the arena moves, so fn/extern/`pub const` decls never
showed the fault — only a module-level `const` after other decls in the same file does.

## Regression window

None. `decl_get_span` is byte-identical at the Aug-10 origin tip (a1f3adeff791) and the parser
locals predate it. The 4edef8fab8e clobber / f1e0fff1662 restore are not involved. The fault is
latent seed behaviour first exposed by the new file shape in `main_lazy_ctx_tools.spl`
(a1c0152c740 / 2e3e763b763, 2026-08-27).

## Fix applied (Simple side, minimal)

Renamed every parser/lint local `decl_span` -> `decl_span_id` (10 sites: `enum_module_body.spl`,
`fn_struct_decls.spl`, `parser_decls_use.spl`, `lint/stub_impl.spl`, `lint/argument_count.spl`).
No contract loosened; `decl_get_span` untouched.

## Defect-class neighbours (recorded, not patched)

Locals named like a `decl_nodes` arena global, outside the parser: `val decl_name` in
`20.hir/hir_lowering/_Items/module_lowering.spl:363` and `10.frontend/core/interpreter/eval_decls.spl:26`.
Not proven to fire (frames are short-lived); listed so a future hit is recognisable.

## Open seed bug

Frame-local vs. cross-module global collision by bare name in `function_exec.rs` publish/refresh.
The seed should key bound globals by `(owner, name)` from the frame's actual import bindings and
never treat a `val`/`var` declared in the frame as a global copy.

## Addendum (verifier neighbour)

# Addendum to doc/08_tracking/bug/seed_interpreter_bare_name_global_publish_clobber_2026-08-28.md

Verifier-noted omission (post-ACCEPT): the defect-class neighbour list should also include

- `src/compiler/20.hir/hir_lowering/_Items/module_declarations_bootstrap.spl:47` —
  `val decl_span = Span.empty()`, reused across the `self.symbols.define(...)` calls in that
  lowering pass. Same hazard shape: a local sharing the bare name of the `compiler.core.ast`
  arena global `decl_span` in a frame that calls back into decl_nodes-owned code. Holds a
  `Span` struct (not the `[i64]` arena), so a publish-back would type-clobber rather than
  truncate; not proven to fire, recorded for recognisability.

The accepted patch's bug record lists only `module_lowering.spl:363` and `eval_decls.spl:26`;
fold this entry into the record when the patch lands (patch itself already accepted, unchanged).
