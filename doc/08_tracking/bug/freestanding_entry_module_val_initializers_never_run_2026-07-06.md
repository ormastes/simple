# Entry-module top-level val initializers never execute under freestanding native-build cranelift

## Status
Open.

## Severity
High — garbage data reads cause immediate triple-fault in ring-3 USEROK smoke.

## Summary
Under freestanding x86_64-unknown-none native-build with `--entry-closure`, top-level `val` initializers in the entry module never execute. Code reads garbage instead of initialized values. Observed: module-level `val USER_CODE_VA` initialized to valid address, but reads yielded RIP 0xc35d... (unmapped), causing triple fault.

Root cause: pure-Simple backend never emits or calls `__module_init_*()` functions for module initialization, matching underlying gap documented in `baremetal_entry_closure_class_instantiation_fault_2026-07-06.md`.

## Evidence
- **Failure site**: `examples/09_embedded/simple_os/arch/x86_64/ring3_smoke_entry.spl` — module-level `val USER_CODE_VA` initialized with address, reads yielded garbage (0xc35d...).
- **Discovery commits**: 12bddd3d29a1, 074fa56278f1 — ring-3 USEROK smoke proves codegen gap.
- **Workaround in place**: moved `val` declarations function-local into `spl_start()` to force eager initialization on entry (commit 074fa56278f1).
- **Related issue**: see `baremetal_entry_closure_class_instantiation_fault_2026-07-06.md` — same root cause (no `__module_init_*` emission).

## Failure Scenario
Any freestanding entry module with top-level `val` or `var` initializers will read uninitialized memory. Ring-3 OS code cannot establish page tables, memory maps, or other setup state if stored in module-level vals.

## Impact
Blocks ring-3 USEROK smoke from using module-level state. Workaround works but not ideal; proper fix requires implementing `__module_init_*` codegen in cranelift lowering for freestanding targets.

## Next Step
Implement `__module_init_*` emission and entry-point invocation in freestanding cranelift backend. Cross-reference with `baremetal_entry_closure_class_instantiation_fault_2026-07-06.md` — both bugs share the same root fix.
