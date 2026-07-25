# WS-C Research: Dice Coefficient Calibration (PROD-003)

Date: 2026-05-15
Analyst: Research Agent (Sonnet 4.6)

---

## 1. Current Threshold Values and Where They Are Defined

File: `src/lib/scv/structural_match.spl`

```
struct StructuralMatchConfig:
    min_dice: i64    # ×1000 fixed-point; paper suggests 500
    min_height: i64  # minimum subtree height for top-down anchoring; paper: 2
    max_size: i64    # skip subtrees larger than this (performance guard)

fn scv_default_match_config() -> StructuralMatchConfig:
    StructuralMatchConfig(min_dice: 500, min_height: 2, max_size: 1000)
```

| Constant   | Value (raw) | Effective value | Location |
|------------|-------------|-----------------|----------|
| `min_dice` | 500         | 0.5 (50%)       | line 23  |
| `min_height` | 2         | 2 levels        | line 23  |
| `max_size` | 1000        | 1000 nodes      | line 23  |

The Dice function returns a ×1000 fixed-point integer (0–1000). The bottom-up
matching loop at line 318 uses `min_dice` as the initial best-score floor:

```
var best_dice: i64 = cfg.min_dice
...
if dice > best_dice:   # strictly greater — ties do NOT match
```

This means any node pair with Dice score ≤ 500 is rejected (not ≥ 500 accepted).

---

## 2. How Thresholds Are Used in the Pipeline

### Top-down phase (`scv_match_top_down`)
- Guard: `base_height < cfg.min_height OR head_height < cfg.min_height` → skip
- Match condition: identical subtree hash (exact content match → Dice = 1.0 implicitly)
- `min_dice` is NOT consulted in the top-down phase; only `min_height` applies.

### Bottom-up phase (`scv_match_bottom_up`)
- For each unmatched base node, iterate all unmatched head nodes
- Compute `scv_dice_similarity(descendant_labels_base, descendant_labels_head)`
- Accept only if `dice > cfg.min_dice` (strictly greater than 500 → effectively > 0.5)
- Take the best-scoring candidate (greedy)

### Edit script generation (`scv_compute_edit_script`)
- Calls top-down then bottom-up, collects all pairs
- Emits Delete (no head match), Insert (no base match), Update (matched, different content), Move (matched, parent mapping differs)

### Merge consumption (`merge.spl` / `scv_pick_merge_line`)
- `scv_try_structural_merge` is called when `scv_structural_merge_applicable` returns true
- Returns "" on failure → falls through to `scv_try_syntax_node_merge` → line merge
- No secondary confidence threshold beyond `min_dice` in the merge path

---

## 3. GumTree Paper Reference Values (Falleri et al., ASE 2014)

The paper "Fine-grained and accurate source code differencing" (Falleri et al.) specifies:

| Parameter        | Paper value | Meaning                                              |
|------------------|-------------|------------------------------------------------------|
| minDice (t)      | 0.5         | Bottom-up similarity threshold                       |
| minHeight        | 2           | Minimum subtree height for top-down anchor           |
| maxSize          | 100         | Skip subtrees with > 100 nodes (perf guard)          |

Notes from paper:
- `t = 0.5` is the default; the paper evaluates sensitivity in range [0.3, 0.7]
- `minHeight = 2` prevents single-leaf nodes from becoming spurious anchors
- The paper's `maxSize = 100` is for their Java evaluation corpus; larger codebases may need higher values

**Current implementation vs. paper:**
| Parameter  | Paper | Current impl | Delta        |
|------------|-------|--------------|--------------|
| min_dice   | 0.5   | 0.5 (500/1000) | **Exact match** |
| min_height | 2     | 2            | **Exact match** |
| max_size   | 100   | 1000         | 10× higher   |

The `max_size = 1000` divergence is intentional: Simple files can be larger than Java
evaluation corpus. This is a performance guard, not a calibration parameter.

---

## 4. Gap Analysis

### Are current values well-calibrated or guessed?

The values for `min_dice` (500) and `min_height` (2) are **directly adopted from the
Falleri et al. paper**, not empirically calibrated against Simple/SCV corpus data.
The source file header comment confirms this: "Thresholds from Falleri et al."

This is reasonable as a starting point but has known limitations:

1. **No corpus validation**: Paper thresholds were calibrated on Java source trees.
   Simple has different node density, naming patterns, and tree shapes.

2. **Strict inequality bug risk**: The bottom-up loop uses `dice > cfg.min_dice`
   (strictly greater). At exactly 0.5, pairs are rejected. In the GumTree paper, the
   condition is `dice >= t`. This is a subtle off-by-one: at exactly 500/1000, a
   valid match is dropped. Whether this matters in practice depends on whether
   equal-Dice ties are meaningful (they usually indicate ambiguous matches, so
   rejecting them may be correct behavior — but it's worth documenting explicitly).

3. **Text-block fallback path**: `scv_structural_diff_text_blocks` (the WS-A fallback)
   does not use `StructuralMatchConfig` at all. Its thresholds are implicit in text
   pattern matching (column-0 fn/class/struct/module definitions). No calibration
   applies to this path.

4. **No near-threshold test cases**: Existing tests exercise:
   - Exact match (top-down, Dice = 1.0) — "high-confidence function move"
   - Complete mismatch / low-confidence — "falls back to conflict for low-confidence partial match"
   The boundary region (Dice ≈ 0.5–0.6) is not tested. It is unknown whether the
   current threshold produces correct behaviour for partially-refactored functions.

5. **TODO dependency**: `TODO(prod-003)` is explicitly blocked on WS-A tree-sitter
   landing. Without structured trees (kind = function_def, etc.), Dice operates on
   text-derived label sets, which are coarser than AST label multisets.

---

## 5. Recommended Calibration Approach

### Test scenarios to add (once WS-A lands)

| Scenario | Expected behaviour | Calibrates |
|----------|--------------------|------------|
| Function with 1 statement changed out of 5 (Dice ≈ 0.80) | Match as Update | Above-threshold |
| Function with 3 of 5 statements changed (Dice ≈ 0.40) | Conflict or no-match | Below-threshold |
| Function with exactly 50% labels shared (Dice = 500) | Document and assert reject/accept | Boundary exactness |
| Identical function moved to another module | Match as Move | Top-down path |
| Function renamed + body unchanged | Match as Update (name change) | Name-vs-body trade-off |
| Two similar stubs, both unmatched before bottom-up | Best-scoring wins, other is Insert+Delete | Greedy correctness |

### Values to adjust

1. **min_dice**: Keep at 500 as paper default. After WS-A lands, run against SCV's
   own commit history (use `scv log` on the SCV repo itself) and measure false-positive
   move detections and false-negative conflicts. Adjust in ±50 steps.

2. **Strict vs. non-strict comparison**: Change `dice > cfg.min_dice` to
   `dice >= cfg.min_dice` to match paper semantics, then add a test at exactly 500
   to confirm boundary behaviour.

3. **max_size**: Current 1000 is a guess. Profile on largest Simple files (compiler
   layers). If matching is fast, raise to 2000; if slow, lower to 500.

---

## 6. Whether TODO Can Be Resolved

**The TODO cannot be resolved yet.** It is correctly blocked on WS-A (tree-sitter
parser) because:

- Without structured AST node kinds (function_def, class_def, etc.), the
  `scv_descendant_labels` function operates on text-derived label sets, which do
  not map to the paper's label multisets. Calibration against such inputs would
  not transfer to tree-sitter output.

**Recommended action**: Keep `TODO(prod-003)` as-is. When WS-A lands:
1. Add boundary test cases listed in Section 5.
2. Run calibration pass against SCV's own commit history.
3. Fix the strict-inequality question (`>` vs `>=`) and document the decision.
4. Resolve the TODO with a commit referencing the calibration data.
