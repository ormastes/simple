# KPF Extended-Enum Sealer Integration — 2026-09-03

## Result

The existing `kpf_closure` integration now has executable mutation evidence for
the two requested seal-time invariants:

- every `Static` or `Complete` constructor provides every required operation;
- a `Dyn` constructor is rejected from a critical sealed composition.

The implementation reuses `PersistentExtensionId`, `Closure`, `TagCapacity`,
and `freeze_universe`; it does not introduce a second identity or closure model.
Generated operation tables remain deterministic and generation-local.

## Evidence

| Check | Result |
|---|---|
| Focused `kpf_closure_spec.spl` | PASS |
| Cache-independent source contract | PASS |
| Disable required-operation rejection | mutation rejected |
| Disable critical `Dyn` rejection | mutation rejected |
| Schema generator and lint files | unchanged |

The mutation runner operates on copies and places transient files under
`SIMPLE_WORKTREE_STORAGE_ROOT`; it never edits the authoritative source.
