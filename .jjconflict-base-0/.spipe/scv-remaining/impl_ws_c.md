# WS-C Implementation: Dice Coefficient Calibration (PROD-003)

Date: 2026-05-15
Engineer: Sonnet 4.6 (WS-C subagent)

---

## Changes Made

### File: `src/lib/scv/structural_match.spl`

**1. Fixed Dice comparison (line ~330, bottom-up matching loop)**

Old:
```
if dice > best_dice:
```

New:
```
if dice >= cfg.min_dice and dice > best_dice:
```

Rationale: The paper (Falleri et al. ASE 2014) uses `dice >= t` (non-strict).
The old code used `best_dice` (initialized to `cfg.min_dice`) as the floor with
a strict `>`, meaning Dice == 500 was always rejected. The new form:
- Accepts Dice >= min_dice (boundary fix, paper-aligned)
- Uses `> best_dice` for tie-breaking (first-wins, preserves greedy stability)

**2. Updated header TODO comment (lines 1–11)**

Extended the comment block to document:
- Thresholds match Falleri et al. defaults (min_dice=500, min_height=2)
- `>=` inequality now matches paper semantics
- max_size=1000 intentional divergence from paper's 100 (Simple files are larger)
- TODO(prod-003) kept as-is; empirical calibration requires tree-sitter AST label
  multisets which are not yet available (blocked on WS-A)

---

## Test Results

| Spec file | Expected | Result |
|-----------|----------|--------|
| `test/02_integration/app/scv_structural_match_spec.spl` | 8/8 pass | EXIT 0 |
| `test/02_integration/app/scv_diff_spec.spl` | 3/3 pass | EXIT 0 |

---

## What Was NOT Changed

- Threshold values (min_dice=500, min_height=2, max_size=1000) — all unchanged
- TODO(prod-003) was kept as a TODO, not converted to NOTE
- No new test cases added (boundary tests deferred to WS-A per research recommendation)

---

## Calibration Status

Thresholds now correctly implement Falleri et al. defaults with correct `>=` semantics.
Empirical calibration against Simple/SCV corpus is deferred until WS-A delivers
tree-sitter WASM parser output with structured node kinds (function_def, class_def, etc.).
