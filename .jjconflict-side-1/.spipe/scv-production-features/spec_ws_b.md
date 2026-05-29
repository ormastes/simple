# SCV Workstream B — Spec Coverage (PROD-003)

**Spec file:** `test/integration/app/scv_structural_match_spec.spl`
**AC covered:** AC-3 (GumTree-grade structural diff and merge)

## It-Block Index

| # | `it` description | AC-3 sub-clause | Requires WS-A? |
|---|-----------------|-----------------|----------------|
| 1 | shows moved named function as move not delete-plus-add in diff | Named anchor — function moved within file; high-confidence top-down match | Yes |
| 2 | shows renamed function as update not delete-plus-add in diff | Named anchor — function renamed in place, body unchanged | Yes |
| 3 | assigns ordinal anchors to unnamed statements reordered within a function | Ordinal anchor — unnamed statement reordering; parent_qpath+index path | Yes |
| 4 | reports high-confidence function move as move in structural diff | High-confidence (identical subtree hash) → "move" not "conflict" | Yes |
| 5 | falls back to conflict for low-confidence partial match in structural merge | Low-confidence Dice match → scv_write_conflict fallback | Yes |
| 6 | gracefully degrades to line merge and logs fallback strategy for kind-line files | Graceful degradation: kind==line → empty anchors → WS-B falls through → line merge; strategy label asserted | Yes (WS-B wiring) |
| 7 | structural 3-way merge applies disjoint named-anchor edits without conflict | Structural 3-way merge; disjoint named anchors → zero conflicts | Yes |
| 8 | structural merge preserves moved function body from left and right edit without conflict | Move + concurrent body edit on same named anchor → apply both, no conflict | Yes |

## WS-A Gate Status

Tests 1–8 are BDD pre-impl specs. They will remain **red** until:
1. WS-A delivers tree-sitter parser output with `kind: function_def` nodes
2. WS-B delivers `src/lib/scv/anchor.spl` + `src/lib/scv/structural_match.spl` + diff/merge extensions

Test 6 requires WS-B to wire `scv_try_structural_merge` into `merge.spl` (so the strategy label is emitted), but the fixture file itself uses only line-level content. The existing line-merge test in `scv_merge_spec.spl` ("line-merges disjoint same-file edits without conflicts") covers pre-WS-B line merge behaviour; test 6 here covers the post-WS-B fallthrough path specifically.

## Threshold Safety

Fixtures for high-confidence tests (1, 4, 7, 8) use **identical bodies** (top-down subtree-hash match) so they are immune to `min_dice`/`min_height` threshold tuning.

Fixtures for the low-confidence test (5) use **completely disjoint bodies** (zero common tokens) to ensure the result is always below any reasonable threshold.

## Proposed Output Contract — Requires Impl Sign-Off

The following output strings are **not** specified in `arch_ws_b.md` — they are proposed by this spec as the observable contract. The implementer must either adopt these exact strings or update the spec to match whatever strings land in the implementation:

| String | Used by test # | Meaning |
|--------|----------------|---------|
| `diff --structural` | 1, 2, 3, 4 | New diff flag enabling structural (GumTree) output |
| `moved <fn_name>` | 1, 4 | Structural diff move label |
| `updated <fn_name>` | 2 | Structural diff rename-in-place label |
| `moved setup.stmt` | 3 | Ordinal anchor reorder label |
| `setup.stmt[0]`, `setup.stmt[1]` | 3 | Ordinal anchor path format |
| `code.spl: structural-anchor-merge` | 7 | Merge strategy log: named-anchor path taken |
| `broken.spl: structural-fallback-line` | 6 | Merge strategy log: WS-B attempted, fell through to line |

## Design Decision Pinned by Test 8

Test 8 asserts that a **positional move (left) + body edit (right) on the same named anchor** resolves to zero conflicts. This is a deliberate design choice: the anchor-aware merger treats positional repositioning as orthogonal to body content. If the design intent changes to require a conflict in this case, test 8 must be updated to `expect(out).to_contain("conflicts=1")`.
