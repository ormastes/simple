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

## Update 2026-07-17 — real root cause pinned; link-stage aggregator landed, codegen gap remains

**Host-side repro (no boot needed, no entry-closure needed):** confirmed this
is NOT specific to freestanding/entry-closure. On the plain HOST hosted
target with a single file:

```simple
fn compute_marker() -> i64:
    40 + 2
val MARKER: i64 = compute_marker()
fn main() -> i64:
    return MARKER
```

`native-build` + run returns `0`, not `42` — the module-level `val`
initializer silently never runs. A control case with a bare literal
(`val MARKER: i64 = 42`) returns `42` correctly.

**Root cause (pinned):** `src/compiler/50.mir/_MirLowering/module_lowering.spl`'s
`lower_const`/`lower_static` (via `lower_const_expr` in
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:3026-3038`)
only const-folds `IntLit`/`FloatLit`/`BoolLit`/`StringLit` — any other
initializer expression (a call, a binop, a field read) returns `nil` and the
binding gets **no runtime initializer at all**: `val` bindings land only in
`MirModule.constants` (dropped if not foldable) and `var` bindings land in
`MirModule.statics` with `init: nil` (zero-initialized BSS, never written).
No codegen backend (LLVM or Cranelift, pure-Simple) ever emits a
`__module_init_*` function body for this case — the concept does not exist
below the MIR layer yet. This reproduces on every native-build target, not
just freestanding/entry-closure; those are just where it's been *noticed*
because the WORKAROUND (moving `val` into a function body) is unavailable or
awkward for OS-level global state.

**What landed (this pass, `src/compiler/70.backend/backend/llvm_native_link.spl`):**
the LINK-STAGE aggregator (`simpleos_module_init_symbols` +
`simpleos_module_init_caller_source`, mirroring the Rust seed's
`generate_init_caller` restored by commit `4aab3c435b7`) — replaces the
riscv64 always-empty `__simple_call_module_inits(){}` stub and adds the same
aggregation to the x86_64 SimpleOS legacy freestanding path, so if/when
codegen starts emitting `__module_init_*` symbols, the linker will discover
and call them. Verified via hand-reproduction of the exact toolchain
invocations (nm/gcc/objdump; see scratchpad transcript) since a compiler
rebuild is out of scope for this pass — **this link-stage fix alone does NOT
make the reproduction above return 42**; the MIR-lowering/codegen gap above
is the actual remaining blocker and needs its own implementation pass
(extend `lower_const`/`lower_static` to lower non-foldable initializers into
a real `__module_init_<prefix>` function body per module, and teach
`expr_dispatch.spl`'s `NamedVar` read path to load a global's address rather
than assuming a folded constant).

**Freestanding/board verification:** not attempted this pass (no rebuild, no
QEMU/board boot per this pass's scope) — remains open per the board-runnable
rule once the MIR-lowering fix lands.
