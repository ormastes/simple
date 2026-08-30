<!-- codex-design -->
# Bootstrap compiler/backend stage split agent tasks

**Status:** design approved; implementation blocked on one admitted success of
the current canonical bootstrap.

| Lane | Ownership | Result |
|---|---|---|
| Manifest | archive/interface/runtime receipts | contracts and sabotage tests |
| Stage 2 | existing canonical pure-Simple compiler build, unchanged | executable and provenance |
| Stage 3 | existing canonical pure-Simple compiler build, unchanged | archive, interface, executable |
| Stage 4 | tool discovery/link | zero compiler compile units |
| Equivalence | system/SPipe evidence | tooling-only equals audit build |

Merge owner owns shared scripts/manifests. Before the admitted baseline,
sidecars may inventory/audit only. After that gate, explicitly non-overlapping
Manifest, Stage-2, Stage-3, Stage-4, and Equivalence implementation lanes may
proceed under merge-owner review. Final review requires the best available
normal/highest-capability model.
