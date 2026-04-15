<!-- codex-research -->
# VS Code Rich Editor Requirements Options

**Feature:** `vscode_rich_editor`  
**Date:** 2026-04-12

## Goal

Ship a whole new VS Code extension that opens `.spl` files in a custom editor
with natural variable-height rendering for math and images.

## Option 1: Math/Image MVP

**Description**
- Keep the new standalone extension package.
- Support `m{}`, `loss{}`, `nograd{}`, `img{}`, and `graph{}` rendering.
- Keep full-document sync for the first release.
- Target a usable custom editor without aggressive hardening.

**Pros**
- Fastest route to a shippable separate extension
- Minimal code churn from the current `src/app/vscode_rich_editor` baseline
- Validates extension packaging and editor UX quickly

**Cons**
- Leaves full-document edit replacement in place
- Duplicate rendered blocks can still collide without identity fixes
- Weaker reliability story for larger files and repeated content

**Effort**
- `S`
- Roughly 4-6 source files plus smoke tests and packaging work

## Option 2: Robust Standalone Rich Editor

**Description**
- Keep the new standalone extension package.
- Use a `CustomTextEditorProvider` with CodeMirror 6 as the primary editor.
- Add stable block identity, block-local edit application, selection sync, and
  deterministic host/webview resync behavior.
- Treat this as the real production path for rich `.spl` editing.

**Pros**
- Best match for the requested product direction
- Preserves `TextDocument` semantics while delivering natural variable-height UI
- Fixes the known correctness risks in the current prototype
- Gives a strong base for later WASM/block-parser integration

**Cons**
- More design and test work than a quick MVP
- Requires explicit sync, identity, and conflict-handling rules
- Needs a real extension test harness, not only visual smoke checks

**Effort**
- `M`
- Roughly 8-12 source files plus tests, docs, and packaging cleanup

## Option 3: Dedicated Rich File Format

**Description**
- Build a new extension and custom editor around a dedicated rich document type
  rather than `.spl` source text.
- Use a separate custom document model and translate to/from `.spl`.

**Pros**
- Maximum layout freedom
- Cleaner long-term authoring model if rich documents become first-class assets

**Cons**
- Breaks alignment with the current text-based Simple workflow
- Requires save/backup/import/export model work
- Highest migration and maintenance cost

**Effort**
- `L`
- Roughly 12-18 source files plus format, lifecycle, and migration work

## Recommended Choice

Choose **Option 2: Robust Standalone Rich Editor**.

It matches the current repo direction, keeps `.spl` as the source format, and
solves the known prototype risks without inventing a new document type.
