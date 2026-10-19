# Interpreter: `vmm_copy.spl` reads `bitfield.spl`'s same-named `PTE_*` constants

- **Filed:** 2026-10-20
- **Status:** OPEN (seed interpreter, name resolution). Not fixed by
  `work/seed-u64-and-dataptr`; that fix made it reachable.

## Symptom

`test/01_unit/os/kernel/memory/vmm_copyin_spec.spl` fails 3/18 in the
interpreter: a cross-page copy reads zeros, an unmapped tail page is accepted,
and a writable-range check dereferences a bogus host address
(`rt_volatile_read_u64 requires a positive non-null host address`).

Inside `src/os/kernel/memory/vmm_copy.spl`, which imports
`PTE_PRESENT, PTE_USER, PTE_WRITABLE, PTE_HUGE_PAGE` from
`os.kernel.memory.vmm` (`1 << 0`, `1 << 2`, `1 << 1`, `1 << 7`), the names
evaluate to `0, 2, 1, 7` — the bit INDICES that
`src/os/kernel/types/bitfield.spl:61-68` defines under the same names.
`vmm_copy.spl` reaches `bitfield` through `os.kernel.types.vmspace_types`
(which imports only bitfield FUNCTIONS). So `(pd_entry & PTE_HUGE_PAGE) != 0`
is true for an ordinary PDE (`... & 7`) and every walk takes the 2 MiB
huge-page branch.

Measured by printing the names at the top of `_vmm_pt_walk` (temporary edit):
`h=7 w=1 p=0 u=2 ps=4096` on both the pre-fix seed and the fixed one. The same
names imported from `vmm` into a standalone probe module read 128/2/1/4.

Before the u64 fix this was masked: `VMM_KERNEL_SPACE_START` was a negative
`Int`, so every walk failed earlier at the user-pointer bound check.

## Class

Bare-name global collision across modules; see
`bare_name_registry_collision_trigger_conditions_2026-07-30.md` and
`binding_module_shadow_census_2026-08-18.md`. This is a concrete in-situ
reproducer for that class.
