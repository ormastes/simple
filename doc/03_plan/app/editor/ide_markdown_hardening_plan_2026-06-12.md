# IDE + Markdown Rendering Hardening Plan

**Date:** 2026-06-12
**Goal:** Harden the Simple IDE (`src/app/ide/`) and its markdown rendering
(`src/lib/editor/`) toward Obsidian-grade robustness, in pure Simple.
**Status:** Phase 1 complete (landed at `a2c1ab3fbda` and the parallel-track
commits beneath it). Phases 2-4 are follow-up work.

## Phase 1 — Parallel hardening sweep (DONE 2026-06-12)

Five scopes hardened by parallel agents, each reviewed and re-verified in
interpreter mode before commit.

| Scope | Files | What landed |
|-------|-------|-------------|
| Render | `src/lib/editor/render/block_model.spl`, `md_renderer.spl` | Obsidian-correct frontmatter (closing `---` required; unterminated `---` renders as horizontal rule), `~~~` tilde fences, `frontmatter` render arm |
| Wiki index | `src/lib/editor/services/md_wiki_index.spl` | `[[`/`![[`/`![` bounds fixes at line end; tags inside code fences no longer indexed |
| MD services | `src/lib/editor/services/md_diagnostics.spl` | Missing `EditorDiagnostic` import fixed; `MdDiagLinkRef` struct replaces mixed-type 4-tuples (interpreter corrupts `.2`/`.3` — bug `md_diag_tuple_element_corruption`, P1); gutted diagnostic specs restored with positive assertions |
| View layer | `src/lib/editor/view/md_editing.spl`, `preview_pane.spl`, `wiki_panel.spl`, `markdown_state.spl` | Link-target scan anchored after `](`, scroll-sync negative-index guard, wiki panel selection clamp, preview/outline toggles |
| IDE app | `src/app/ide/*.spl` | Empty/unknown argv → help + exit code, capability validators, plugin manifest validation (empty name/version, duplicates), db-admin `:memory:` fallback, slides/sheets empty-doc probes, GUI bounds check |

Verification: editor unit suite 352 passed (9 pre-existing failures, see
Phase 2); IDE suite 77/77. New specs: frontmatter (14), extended callouts (30),
wiki-index hardening (35), view-layer (45), 7 `ide_*_harden_spec.spl` files.

## Phase 2 — Fix pre-existing failing editor specs

9 failures in 4 files, present at baseline `37d11d8da27` (not caused by
Phase 1; verified via empty diff on those areas):

- `test/01_unit/lib/editor/editor_path_text_spec.spl`: 3 passed, 2 failed
  (`keeps GUI shell path and payload helpers in shared lib`,
  `keeps reusable editor modules on shared path helpers`).
- `test/01_unit/lib/editor/host_simpleos_surface_contract_spec.spl`: 3
  passed, 5 failed (`documents host adapters outside the SimpleOS-safe path`,
  `documents legacy VS Code docs pointed at current shared IDE surfaces`,
  `wraps editor GUI HTML for pure Simple web before host presentation`,
  `documents the live editor MCP subset without overclaiming the full catalog`,
  `documents pure Simple render proof separately from Tauri shell proof`).
- `test/01_unit/lib/editor/multi_buffer_spec.spl`: 0 passed, 1 failed
  (file-level failure).
- `test/01_unit/lib/editor/split_pane_spec.spl`: 0 passed, 1 failed
  (file-level failure).

Native-mode root-cause probes point at
`src/lib/nogc_sync_mut/editor/panels/inspector.spl` field inference for
`SceneNodeData.sprite_texture` and `src/lib/editor/70.backend/gui_backend.spl`
`ANY.selected_index` / wrapper inference. Fix those lowering blockers before
rerunning the four focused specs.

Root-cause each (no skip/weakening per no-cover-up rule). Run with
`SIMPLE_BOOTSTRAP_DRIVER=bin/release/x86_64-unknown-linux-gnu/simple_seed`.

## Phase 3 — Compiler: interpreter 4-tuple corruption (P1)

Bug `md_diag_tuple_element_corruption`: `.2`/`.3` access on
`[(i64, i64, text, text)]` returns corrupted values in the interpreter
(text → `<value:0x..>` pointer, `trim().len()` → -1). The `MdDiagLinkRef`
struct workaround stays regardless; the interpreter bug needs a compiler-side
fix plus a regression spec on mixed-type 4-tuple arrays.

## Phase 4 — Obsidian parity extensions (markdown rendering)

Candidate next features, roughly by value:

1. **Block references** — `[[note#^block-id]]` link resolution + `^block-id`
   anchors in the wiki index.
2. **Embed rendering** — DONE 2026-06-12. `![[note]]` transclusion already
   existed via the wiki render path; `![[note#heading]]` heading-scoped
   transclusion added (`md_wiki_heading_section`, exact trimmed-title match
   with case-insensitive doc-title fallback — slug comparison is unreliable,
   see bug `md_slugify_string_corruption` P1).
3. **Footnotes** — `[^1]` definitions/references in block model + renderer +
   diagnostics for undefined footnotes.
4. **Nested callouts** — callout-inside-callout in `block_model.spl`.
5. **Math blocks** — DONE 2026-06-12. `$$ ... $$` (multi-line, single-line,
   unterminated-to-EOF) parse as `math` blocks; verbatim render with dim
   delimiters and styled body. No formula layout (future work if wanted).
6. **Table column alignment** — DONE 2026-06-12. Cells padded to a uniform
   column grid honoring `:--`/`:-:`/`--:` separator markers; short rows
   padded with empty cells.
7. **Backlinks panel** — reverse-link view over the existing wiki index.

Each item: implement in pure Simple, spec in interpreter mode, review before
commit.
