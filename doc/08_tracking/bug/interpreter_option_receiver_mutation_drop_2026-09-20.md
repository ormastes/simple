# Interpreter drops class-field mutations through option-typed (`T?`) receivers

- Status: OPEN (2026-09-20) — characterized by the GPU FFI loader lane; root cause is seed-side (off-limits per project rules). Pure-Simple compiler fix needed.
- Found: 2026-09-20 (unmasked by fixing `gpu_ffi_loader_probes_linux_sonames_on_macos_2026-09-19.md`)
- Component: tree-walk interpreter lane used by `bin/simple test` (the lane the test runner selects); seed runtime.

## Observation

When a factory returns an option type (`create_dynamic() -> VulkanDynFfi?`), mutating through the receiver (`ffi.init()`) operates on a temporary copy: the write lands nowhere observable. Characterization probes (2026-09-20):

- Nullable receiver (`T?`) → mutation lost.
- Direct constructor receiver → mutation persists.
- `x!` force-unwrap → still a copy; mutation lost.
- Map/array fields through the option receiver → also lost.

Same defect family as `jit_class_mutation_drop_characterization_2026-07-04.md`, but that entry covers the JIT lane; this is the interpreter lane and the option-typed receiver shape specifically. Any `T?`-returning factory whose callers mutate is affected; specs that only assert on return values (not mutated ledger state) can pass while silently never exercising the mutation.

## Workaround in tree

`src/lib/nogc_sync_mut/gpu/engine2d/ffi_vulkan.spl` now boxes the ledger behind per-instance `AtomicI64` handles (`std.nogc_sync_mut.atomic`), which mutate runtime-owned storage and survive receiver copies; `last_rejection()` round-trips through a fixed op-code table (`_reject_op_code`/`_reject_op_name`). This is a targeted workaround, not a general fix.

## Fix direction

1. In the interpreter's method-call lowering for option-typed receivers, bind the unwrapped payload by reference (or write back the mutated payload into the option slot) instead of copying.
2. Add a spec: class with mutable field, factory returning `T?`, mutate through receiver, assert observable change — in both interpreter and JIT lanes.

## Related

- `jit_class_mutation_drop_characterization_2026-07-04.md` (JIT-lane sibling)
- `gpu_ffi_loader_probes_linux_sonames_on_macos_2026-09-19.md` (the lane that surfaced this)
