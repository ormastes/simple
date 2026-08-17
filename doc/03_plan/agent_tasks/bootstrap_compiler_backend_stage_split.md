<!-- codex-design -->
# Bootstrap compiler/backend stage split agent tasks

**Status:** design approved; implementation blocked on one admitted success of
the current canonical bootstrap.

| Lane | Ownership | Result |
|---|---|---|
| Manifest | archive/interface/runtime receipts | contracts and sabotage tests |
| Stage 2 | Cranelift compiler | executable and provenance |
| Stage 3 | LLVM compiler | archive, interface, executable |
| Stage 4 | tool discovery/link | zero compiler compile units |
| Equivalence | system/SPipe evidence | tooling-only equals audit build |

Merge owner owns shared scripts/manifests. Sidecars may inventory only; final
review requires the best available normal/highest-capability model.
