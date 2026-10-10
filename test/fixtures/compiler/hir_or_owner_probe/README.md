# Imported OR subject-owner regression

Producer baseline SHA: `0e5695a3fb071b621eb3a2088fe9df08ce7e06f1f568da6288f2f2136fe62079` (source `5e94f455`). Bootstrap mode was explicitly `SIMPLE_BOOTSTRAP=1`.

Baseline receipts: `/mnt/c/Temp/simple-hir-or-owner-baseline-ready-20261010/validation` at fixture commit `36317e560`. Bare imported `A | B` failed HIR with `[A] vs [B]`; genuine payload mismatch rejected `[x] vs [y]`. The qualified and payload main modules compiled, but their enum-only provider hit the separate empty-MIR rejection.

Control receipts: `/mnt/c/Temp/simple-hir-or-owner-control-20261010/validation` at fixture commit `b8ad976c9`. Adding a called provider function made qualified object/link/run succeed, but stdout was `1/1/1` rather than `1/1/0`. This is a distinct observed native dispatch failure; its first-loss owner is unproven (frontend optional payload transport is also under investigation). The HIR repair does not claim to fix it. The payload control then failed HIR with unresolved `x`, another unresolved control failure.

The proposed production change only carries the existing subject type through direct/nested OR alternatives before strict binding-set validation. It does not alter enum payload lowering, MIR dispatch, name maps, mutable binding handling, or validation rules.

## Required candidate assertions — UNEXECUTED

| Fixture | Required outcome |
| --- | --- |
| bare | Object/link/run exit 0; stdout `1\n1\n0\n` |
| qualified | Object/link/run exit 0; stdout `1\n1\n0\n`; payload P must not match unit A/B |
| nested | Object/link/run exit 0; stdout `1\n1\n0\n` |
| payload (separate known failure; not claimed repaired) | Object/link/run exit 0; stdout `17\n29\n0\n` |
| mismatch | Build exit 1, no object, named `or-pattern alternatives must bind the same variables` diagnostic |

The companion HIR unit spec is also UNEXECUTED. No full Phase3 rerun or candidate admission is implied. Earlier baseline evidence remains tied to its original fixture commits; these current providers include a called function to avoid the separate empty-module rejection.

The nested native fixture syntax is UNEXECUTED; the focused HIR regression constructs nested OR AST nodes directly and asserts exact alias IDs, enum variant names, nesting, and wrapper typing. The known-failing payload positive is retained as a separate native diagnostic fixture, not a passing unit requirement of this narrow repair.
