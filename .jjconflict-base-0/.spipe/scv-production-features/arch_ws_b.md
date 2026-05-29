# SCV Workstream B Architecture: GumTree-Grade Structural Diff/Merge (PROD-003)

## 1. Module List

| File | Status | Owns |
|------|--------|------|
| `src/lib/scv/structural_match.spl` | NEW | Anchor extraction, top-down/bottom-up matching, edit script |
| `src/lib/scv/anchor.spl` | NEW | Anchor type definitions, qualified-name builder |
| `src/lib/scv/diff.spl` | MODIFY | Call `scv_compute_edit_script` for intra-file move detection |
| `src/lib/scv/merge.spl` | MODIFY | Replace `scv_try_syntax_node_merge` with anchor-aware strategy |

WS-B does NOT modify `parser.spl` (WS-A boundary). Consumes `scv_syntax_node_children` + object schema only.

---

## 2. Key Interfaces

### 2a. Anchor Types (`anchor.spl`)

```
# Tagged variant — no inheritance
# Named: survives positional change (function, class, module by qualified name)
# Ordinal: unnamed statement/expr, stable within parent

struct NamedAnchor { qpath: text }          # e.g. "mod.ClassName.method_name"
struct OrdinalAnchor { parent_qpath: text, index: i64 }  # e.g. "mod.fn.stmt[2]"

# Caller uses kind field to dispatch
struct Anchor { kind: text, named: NamedAnchor, ordinal: OrdinalAnchor }
```

### 2b. Anchor Extraction (`structural_match.spl`)

```
# Returns empty list for fallback line nodes (kind == "line") → graceful degradation
fn scv_extract_anchors(root: text, node_id: text, parent_qpath: text) -> [Anchor]

# Load a syntax node object from store; returns empty on missing
fn scv_load_node_fields(root: text, node_id: text) -> text   # raw .sdn text
fn scv_node_kind(node_fields: text) -> text
fn scv_node_syntax_hash(node_fields: text) -> text
```

### 2c. Config (`structural_match.spl`)

```
# Thresholds: defaults TBD — consult Falleri et al. before hardcoding values
struct StructuralMatchConfig {
    min_dice: i64,     # × 1000 fixed-point; paper suggests ~500; TBD
    min_height: i64,   # minimum subtree height for top-down anchoring; paper: 2; TBD
    max_size: i64      # skip matching subtrees larger than this; TBD
}

fn scv_default_match_config() -> StructuralMatchConfig
```

### 2d. Subtree Hash + Dice (`structural_match.spl`)

```
# Recursive subtree hash from node's syntax hash + children hashes
fn scv_subtree_hash(root: text, node_id: text) -> text

# Descendant label multiset as sorted join of leaf text values
fn scv_descendant_labels(root: text, node_id: text) -> [text]

# Dice(A,B) = 2|A∩B| / (|A|+|B|); returns × 1000 fixed-point
fn scv_dice_similarity(a: [text], b: [text]) -> i64
```

### 2e. Top-Down + Bottom-Up Matching (`structural_match.spl`)

```
# Phase 1: identical subtree hashes → high-confidence anchors
fn scv_match_top_down(
    root: text,
    base_root: text, head_root: text,
    cfg: StructuralMatchConfig
) -> [(text, text)]   # list of (base_node_id, head_node_id) pairs

# Phase 2: unmatched nodes by Dice similarity on descendant labels
fn scv_match_bottom_up(
    root: text,
    base_root: text, head_root: text,
    existing: [(text, text)],
    cfg: StructuralMatchConfig
) -> [(text, text)]
```

### 2f. Edit Script (`structural_match.spl`)

```
# Edit operation kinds: "insert" | "delete" | "update" | "move"
struct EditOp { kind: text, base_node: text, head_node: text, anchor: Anchor }

# Consumed by both diff display and merge strategy
fn scv_compute_edit_script(
    root: text,
    base_root: text, head_root: text,
    cfg: StructuralMatchConfig
) -> [EditOp]
```

### 2g. Structural Merge Entry Point (`merge.spl` extension)

```
# Replaces/extends scv_try_syntax_node_merge
# Returns merged text or "" to fall through to line merge
fn scv_try_structural_merge(
    root: text,
    base_root: text, left_root: text, right_root: text,
    cfg: StructuralMatchConfig
) -> text

# Move detection: matched node whose parent mapping differs from base
fn scv_classify_edit_op(op: EditOp, base_matches: [(text, text)]) -> text
    # returns "move" | "update" | "insert" | "delete" | "conflict"
```

---

## 3. Data Flow

```
[parser_index.sdn]  ←─ WS-A produces; WS-B reads only
        │
        ▼
scv_extract_anchors()        # walk children graph via scv_syntax_node_children()
        │                    # fallback kind==line → empty anchor list
        ▼
scv_match_top_down()         # identical subtree hashes → anchor pairs
        │
        ▼
scv_match_bottom_up()        # Dice on descendant labels → additional pairs
        │
        ▼
scv_compute_edit_script()    # insert/delete/update/move per node
        │
     ┌──┴────────────┐
     ▼               ▼
 diff.spl         merge.spl
 (move display)   (scv_try_structural_merge)
                       │
          high-conf → apply move/update
          low-conf  → scv_write_conflict (existing path)
```

---

## 4. Graceful Degradation

| Parser output | Anchor extraction result | Matching behavior |
|---------------|--------------------------|-------------------|
| `kind: line` (fallback) | `[]` empty | top-down: no anchors; bottom-up: no Dice candidates → `scv_compute_edit_script` returns `[]` → `scv_try_structural_merge` returns `""` → caller falls through to existing line merge |
| `kind: function_def` etc (tree-sitter, WS-A) | Named + Ordinal anchors | Full GumTree matching |
| Mixed (partial parse_error) | Anchors from parsed subtrees only | Partial matching; unparsed regions fall to line merge |

No special-case code required for fallback — empty anchor list naturally falls through.

---

## 5. File Ownership (Disjoint from Other Workstreams)

| Workstream | Files owned |
|------------|-------------|
| WS-A | `parser.spl`, `parser_registry.spl`, tree-sitter integration |
| **WS-B** | `structural_match.spl` (new), `anchor.spl` (new), `diff.spl` (extend), `merge.spl` (extend) |
| WS-C | Conflict UX / resolution commands |
| WS-D | Remote sync, object transfer |
| WS-E | Gate/fsck hardening |

Cross-file move scope: **per-file-pair only** (piggybacks on `scv_diff_emit_renames` rename map).
Whole-repo O(N²) matching is out of scope — document as known limitation.

---

## 6. Key Dependencies and Risks

- **WS-A dependency**: `scv_syntax_node_children` exists (confirmed in parser.spl). Named `kind` values from tree-sitter (e.g. `function_def`) required for Named anchors; WS-B is blocked on WS-A delivery for non-fallback files.
- **Threshold values**: Do NOT hardcode `min_dice`/`min_height` — consult Falleri et al. paper cited in `doc/01_research/domain/scv.md` before setting defaults in `scv_default_match_config`.
- **No inheritance**: all variants are structs with `kind: text` discriminant.
- **Specs to add**: `test/integration/app/scv_structural_match_spec.spl` — function moved to different file, function renamed in place, unnamed statement reordering, low-confidence → conflict fallback.
