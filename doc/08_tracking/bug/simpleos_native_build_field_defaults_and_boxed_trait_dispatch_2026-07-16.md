# Bug: entry-closure cranelift — omitted `= nil` field defaults retain garbage; trait dispatch on boxed SoftwareBackend faults

- **Status update (2026-07-16, later):** Symptom A ROOT-FIXED in `6b59a8c4bf7` —
  NOT entry-closure-specific: BOTH HIR struct-construction sites (brace form in
  `collections.rs::lower_struct_init`, paren form in `calls.rs` which lowered
  named args as POSITIONAL initializers) emitted fields in source-literal order
  while MIR/codegen zip values against the FULL DECLARED field list — omitting
  interspersed defaulted fields shifted every later value into the wrong slot
  and left tail fields as heap poison. Fix: shared `lower_struct_init_fields`
  resolves declared order (registry + cross-module `global_struct_defs`
  fallback), matches named args by name, nil-fills omissions. Hosted repro
  (both forms) confirmed wrong-before/correct-after; positional and
  out-of-order-named regression checks pass. **Symptoms A and B are TWO
  separate roots.** B remains OPEN: `SoftwareBackend`'s `impl RenderBackend`
  IS registered in its declaring module (`HIT type_id=TypeId(155)`,
  instrumentation-verified) — remaining hypothesis is
  `ctx.vtable_type_ids.get(type_id)` resolution at the SoftwareBackend
  struct-init codegen site, or the emitted vtable data object being stripped
  by `--gc-sections` despite registration. The fault cluster after
  `launcher apps=15` now follows the SECOND `create_offscreen()` (the first no
  longer faults post-A-fix).
- **Date:** 2026-07-16
- **Severity:** critical (LAST blocker for SimpleOS x86_64 desktop first frame — screendump still black)
- **Component:** rust seed codegen (cranelift, `native-build --entry-closure`, freestanding)
- **Related:** sibling entry-closure codegen bugs fixed same day: `86e56ca7867` (Result.Ok routing), `610b4572a32` (Try-operator strip), `77c519cdab43` (trait-impl virtualization scope). Mitigations for THIS bug landed in `4c1a5365c61` (call-site field pinning) — root fix still owed.

## Symptom A — field defaults not applied (workaround landed, root open)
`Engine2D`'s optional accelerator fields (`vulkan_backend`, `cuda_backend`,
`metal_backend`, `opencl_backend`, `font_renderer`) declare `= nil` defaults.
Under the entry-closure cranelift path, constructing with those fields omitted
leaves them holding **garbage/poison memory**, observed live: wild-RIP crash in
`Engine2D.draw_rect_filled`'s `vulkan_backend` branch (traced by serial print
bisection). Workaround in `4c1a5365c61`: explicitly pin the fields to `nil` in
`create_offscreen()`, `create_with_baremetal_backend_dims()`,
`create_with_virtio_gpu_backend()`. Root fix: make omitted-field default
initialization reliable in the seed codegen (verify where struct literals
lower defaults; suspect the defaults are skipped for fields whose type erased
to ANY/optional in closure-discovered modules).

## Symptom B — trait dispatch on boxed SoftwareBackend faults (OPEN, blocks first frame)
After `launcher apps=15`, `shell.render_baremetal_first_frame(...)`
deterministically dies: dozens of low-address faults (`rip≈0x69xx`) against a
fixed high canonical `cr2` (`0xffffffffb58a....`) — stack-corruption-like,
QEMU exits. Always preceded by `[heap] alloc sz=0x800020
caller=rt_array_repeat+0x76` = an `Engine2D.create_offscreen()`
(SoftwareBackend, ~8MB buffer) for an embedded surface needing real alpha
blending (the taskbar was exempted by direct routing in `4c1a5365c61`, this
one cannot be). Pinned shape: **`self.backend.method()` generic trait dispatch
faults whenever `self.backend` is a `SoftwareBackend` boxed via
`create_offscreen()`** (Engine2D has `baremetal_backend`/`virtio_gpu_backend`
shortcut fields that route around dispatch; no `software_backend` shortcut).

Note Symptoms A and B are plausibly the SAME root: if omitted/optional fields
hold poison, the boxed trait-object's vtable/data words may be poisoned the
same way.

## Fix directions
1. **Root (preferred):** in the seed, find why struct-literal lowering skips
   `= nil` defaults for omitted fields under entry-closure (Symptom A), and
   whether trait-object boxing for closure-discovered impls emits a bad
   vtable/data pair (Symptom B). The `77c519cdab43` local_trait_impls change
   is adjacent — check `create_offscreen`'s SoftwareBackend impl is in the
   local set and its vtable survives section-GC.
2. **OS-side stopgap (if root drags):** add a `software_backend` shortcut
   field to Engine2D mirroring the existing baremetal/virtio pattern
   (~15 dispatch methods + ~20 constructors — heavy; only with approval).

## Repro
Full kernel build + QEMU boot per
`doc/08_tracking/bug/simpleos_native_build_bare_len_dynamic_dispatch_symbol_collision_2026-07-16.md`
recipe; watch serial after `launcher apps=15`. Last-known serial:
`build/os/_wk/serial.log`; screendumps `build/os/_wk/shot25*.ppm` (0.00%).
