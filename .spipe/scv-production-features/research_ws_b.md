# SCV Workstream B: GumTree-Grade Structural Diff/Merge (PROD-003)

**Date:** 2026-05-15  
**Sources:** `src/lib/scv/diff.spl`, `src/lib/scv/merge.spl`, `src/lib/scv/parser.spl`,
`doc/05_design/scv.md`, `doc/01_research/domain/scv.md`, test specs below.

---

## 1. Current Diff Architecture

**File:** `src/lib/scv/diff.spl` (163 lines)

The diff pipeline is flat and text-driven:

- `scv_diff(root, mode)` walks the working copy against the stored index.
- Each file gets a `content_id` (hash); unchanged files are skipped.
- Rename detection: `scv_diff_emit_renames` matches deleted+added pairs by exact
  content hash (`scv_diff_row_chunk`). First exact-content match wins. No fuzzy matching.
- Policy views: `--syntax` (line-numbered), `--ignore-trailing-space`, `--ignore-formatting`
  (collapses horizontal whitespace; skips Python/YAML/Makefile/Markdown paths).
- `scv_diff_same_under_mode` re-hashes content under the selected view before marking modified.

**No intra-file structural diff exists.** "modified" is a binary flag — no hunks, no move detection within a file.

---

## 2. Current Merge Architecture

**File:** `src/lib/scv/merge.spl` (331 lines)

Three-way merge with conflicts as data. Merge order (from design doc):

1. Identical content → return either side
2. One side unchanged from base → take the other
3. File add/delete conflict → record as conflict object
4. Exact-content rename + opposite-side edit → preserve edit at moved path (`left-rename-right-edit` strategy)
5. Disjoint syntax-node fallback merge (same-shape text, `scv_try_syntax_node_merge`)
6. Disjoint line fallback merge
7. Overlapping leaf edits → record conflict

Key functions: `scv_pick_merge_line`, `scv_try_syntax_node_merge`, `scv_write_conflict`,
`scv_apply_line_side`, `scv_write_merged_line_file`, `scv_line_changes_overlap`.

**Explicit design note:** "Move handling is bounded to exact-content file moves. Tree-sitter
field-aware or GumTree-style move matching is deferred."

---

## 3. Syntax Node Storage

**File:** `src/lib/scv/parser.spl`

Syntax nodes are stored as text objects under `.scv/objects/syntax/` via `parse-gate`.
Node schema (from design doc):

```
grammar: fallback-line|fallback-binary|tree-sitter-...
version: <grammar version>
execution: fallback-line|fallback-binary|tree-sitter
kind: file|line|chunk|...
field: <optional field name>
children: <comma-separated syntax node ids>
path: <repo-relative path, for roots>
language: <language id>
raw: <raw content id>
syntax: <syntax hash>
semantic: <policy hash>
parse_status: parsed_ok|parsed_error|missing
```

**Fallback line-node identity:** content-addressed by `(line number, byte range, line text)`.
Unchanged same-position lines keep their node IDs across edits. Root recorded in `parser_index.sdn`.

Cache: `parse-gate` checks existing index for same `(path, raw_hash, language, parser_identity)` before rebuilding.

---

## 4. Reusable Extension Points for PROD-003

| Component | Current Role | PROD-003 Hook |
|---|---|---|
| `scv_try_syntax_node_merge` | Disjoint line-node merge | Replace/extend with anchor-aware matching |
| `scv_diff_emit_renames` | File-level exact rename | Extend to intra-file subtree moves |
| `scv_pick_merge_line` | Per-file merge strategy dispatch | Add `structural-move` strategy |
| Syntax node schema | Stores `kind`, `children`, `field` | Already representable as GumTree input |
| `parser_index.sdn` | Root node per file | Entry point to walk the tree |

The `children` + `kind` + `field` schema is sufficient to represent a tree input to GumTree.
What's currently missing: (a) richer `kind` values from a real parser (fallback only has `line`, `chunk`, `file`), and (b) a matcher that walks `children` graph.

---

## 5. GumTree Algorithm Requirements (External Prior Art)

Domain research cites two sources:
- **GumTree** (Falleri et al.): top-down greedy matching by Dice similarity on descendant label multisets, then bottom-up propagation. Produces: insert/delete/update/move edit operations.
- **ChangeDistiller** (Fluri et al.): fine-grained change classification.

Source papers: `doc/01_research/domain/scv.md` cites PDFs — specific algorithmic parameters (similarity thresholds, etc.) are in the papers, not in the repo. Do not hard-code thresholds without consulting the paper.

Key GumTree requirements for PROD-003:
1. Tree input with typed nodes (`kind`) and string labels (node text)
2. Top-down phase: match nodes with identical subtree hashes as anchors
3. Bottom-up phase: match unmatched nodes by Dice similarity on descendant label multisets
4. Move detection: a matched node whose parent mapping differs from base is a move
5. Confidence: Dice threshold separates high-confidence moves from low-confidence (fallback to conflict)

---

## 6. PROD-003 Anchor Model

PROD-003 specifies two anchor types:

- **Named anchors** (functions, classes, modules): qualified name path, e.g. `mod.ClassName.method_name`
- **Unnamed anchors**: `parent_anchor + ordinal`, e.g. `mod.fn.stmt[2]`

**This is a node-identity extension**, not just a diff algorithm change. Current fallback line nodes
use positional identity `(line_no, byte_range, text)` — sufficient for unchanged lines but breaks
when code moves. Named anchors must survive positional changes.

For merge: high-confidence structural match (above Dice threshold) → show as move.
Low-confidence → record as conflict (same as current `scv_write_conflict` path).

---

## 7. Constraints and Risks

### CRITICAL: Tree-sitter Dependency
The fallback parser (`kind: line`) has no semantic structure — no function/class/module
boundaries. **PROD-003's named anchors require AST node kinds that only a real parser produces.**

Three options (must be decided before implementation):
- **Option A (Recommended): Layer on Slice 5 Tree-sitter.** PROD-003 gates on Tree-sitter landing.
  Cleanest; reuses `parser_index.sdn` with richer `kind` values. Aligns with design intent.
- **Option B: Pure-Simple AST extractor for a subset (e.g., `.spl` only).** Avoids Wasm dependency
  but narrows scope. Risk: ad-hoc parser diverges from real grammar.
- **Option C: Best-effort on fallback `line` nodes.** Unnamed anchors only. Named anchor requirement
  is unmet — PROD-003 spec cannot be fully satisfied without semantic node kinds.

### Other Risks
- `TSNode` pointers invalid after edit (design doc warning): SCV already owns syntax node IDs;
  Tree-sitter pointers must not be stored as SCV identity. Already addressed in design.
- Grammar version changes invalidate syntax node IDs: cache miss on version change is correct
  behavior; document as expected.
- Dice threshold is a research parameter; wrong value → too many conflicts or false-positive moves.
  Recommend starting at Falleri et al.'s published default and tuning against test cases.

---

## 8. Test Coverage Gaps

Current specs: `test/02_integration/app/scv_diff_spec.spl`, `test/02_integration/app/scv_merge_spec.spl`

Covered:
- Raw/syntax/formatting policy diff views
- Exact-content rename detection (file level)
- Edit-across-rename merge (`left-rename-right-edit`)
- Conflict recording and resolution

**Not covered (needed for PROD-003):**
- Function moved to different file (same name, different path)
- Function renamed in place
- Unnamed statement reordering within a function
- Low-confidence match → conflict fallback
- Cross-language anchor stability

---

## 9. Implementation Approach

1. **Gate on Tree-sitter (Option A):** Do not start PROD-003 implementation until Slice 5 parser
   lands. If earlier delivery is required, scope to `.spl`-only via Option B.
2. **Extend syntax node schema:** Add `anchor: <qualified-name-or-parent-ordinal>` field to
   named/unnamed nodes. `parse-gate` populates anchor from Tree-sitter CST field names.
3. **New module `src/lib/scv/structural_matcher.spl`:** Implements top-down + bottom-up GumTree
   phases. Input: two `parser_index.sdn` root node trees. Output: match map + edit script.
4. **Extend `scv_pick_merge_line`:** Add `structural-move` strategy that calls structural matcher;
   falls back to existing `scv_write_conflict` on low confidence.
5. **Extend `scv_diff_emit_renames`:** After file-level rename pass, run structural matcher on
   same-file before/after to emit intra-file `moved <anchor> from <path>:<line> to <path>:<line>`.
6. **Test-first:** Write spipe specs for each anchor type before implementation.

---

**Key file paths:**
- `src/lib/scv/diff.spl`
- `src/lib/scv/merge.spl`
- `src/lib/scv/parser.spl`
- `doc/05_design/scv.md` (Merge Design + Fallback Parser sections)
- `doc/01_research/domain/scv.md` (Structural Diff section)
- `test/02_integration/app/scv_diff_spec.spl`
- `test/02_integration/app/scv_merge_spec.spl`
