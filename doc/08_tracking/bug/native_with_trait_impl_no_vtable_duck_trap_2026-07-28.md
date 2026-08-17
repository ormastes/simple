# `class X with Trait` registers no vtable — native trait calls trap on `ud2`

- **Status:** source-side fix landed for the Draw IR executor; compiler gap OPEN
- **Found:** 2026-07-28, SimpleOS-WM showcase cell (guest render fault)
- **Related:** `jit_game2d_backend_method_dispatch_sigsegv_2026-07-02`

## Symptom

The SimpleOS WM guest booted, negotiated the host GPU
(`result=fallback backend=software`), then died with `reason=guest-render-fault`,
1 exception frame, and every frame marker at zero (`first-frame-rendered`,
`desktop-ready`, `production-readiness`, `content-presented`).

Faulting `rip` decoded to `0f 0b` (`ud2`) inside
`engine2d_draw_ir_render_batch_embedded`, immediately preceded by
`lea rdi,[rip+...]; mov esi,0xd2; call rt_eprintln_str`.

## Root cause

`mov esi,0xd2` = 210 bytes, which is **byte-exactly** the length of the
duck-dispatch diagnostic in
`src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs:1410`. That
confirms the trap is `compile_method_call_virtual`'s
`DUCK_DISPATCH_UNSUPPORTED_SLOT` sentinel path, not a nil-receiver guard.

The sentinel is chosen in
`src/compiler_rust/compiler/src/mir/lower/lowering_core.rs:947`
(`find_trait_for_method_on_receiver`): when a receiver is *statically typed as a
trait*, the slot comes from `slot_for`, which returns the sentinel unless
`dependency_graph.get_implementations(trait_name)` is non-empty.

Only the `impl Trait for Type` form populates that map. The **mixin form
`class X with Trait` does not**, so a trait whose only conformances are mixins
looks impl-less: every trait-typed call lowers to the trap.

`DrawIrRenderTarget` has exactly two conformances, both mixins:

- `src/lib/gc_async_mut/gpu/engine2d/engine.spl:181` — `class Engine2D with DrawIrRenderTarget`
- `src/lib/gc_async_mut/gpu/engine2d/draw_ir_target_metal.spl:32` — `class MetalDrawIrRenderTarget with DrawIrRenderTarget`

Commit `bb8da88ebf2` ("refactor(engine2d): decouple Draw IR render target")
retyped the whole Draw IR advanced executor from concrete `Engine2D` to the new
`DrawIrRenderTarget` trait. That commit introduced the trap: after it, every
`eng.width()`, `eng.backend_name()`, `eng.read_pixels_with_source()` etc. inside
`_engine2d_draw_ir_render_batch_embedded` was a trait-typed call with no vtable.

## Fix applied (Simple source)

Restored concrete `Engine2D` typing in
`src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl` (32 references) and
repointed the import to `std.gc_async_mut.gpu.engine2d.engine.{Engine2D}`.

With a concrete receiver, `find_trait_for_method_on_receiver` takes the
`available_functions.contains("Engine2D.<method>")` branch and returns `None`,
which devirtualizes to a direct call. Verified that `Engine2D` concretely
defines **all 31** `DrawIrRenderTarget` methods, so every site devirtualizes;
none falls through to the `local_trait_impls` branch.

`Engine2D.draw_ir_create_offscreen` returned `Result<DrawIrRenderTarget, text>`,
which would have re-introduced a trait-typed surface for the offscreen
composite path. Since all three of its branches
(`create_shared_vulkan_offscreen`, `create_shared_metal_offscreen`,
`create_offscreen`) already return `Engine2D`, the trait return was a pure
widening. Added `draw_ir_create_offscreen_engine` returning
`Result<Engine2D, text>` and made the trait method delegate to it, so the trait
signature is untouched and conformance cannot regress.

## Why not "make the trait register a vtable"

Registering mixin conformances into `dependency_graph` would enable *real* slot
dispatch — but no constructor emitted by the mixin path ever **writes** a vtable
pointer into the object. Real slot dispatch would then read field data as a
function pointer and jump to garbage. That converts a loud, diagnosable `ud2`
into a silent wild jump: strictly worse. The codegen comment at
`lowering_core.rs:937-945` says exactly this.

The correct compiler fix is larger than registration alone: the mixin form must
also *emit and populate* a vtable. Until then the sentinel is the right
behaviour and source must use concrete typing on native/freestanding lanes.

## Open compiler gap

`class X with Trait` silently produces a type that satisfies the type checker
but traps on every trait-typed dispatch in native builds. Options, in order of
preference:

1. Emit + populate vtables for mixin conformances, then register them.
2. Reject trait-typed values of mixin-only traits at compile time on native
   targets, with a diagnostic naming the trait, so this fails at build time
   rather than as a runtime `ud2`.

Until one lands, **do not introduce trait-typed parameters for traits whose only
conformances are `with` mixins** on any native or freestanding lane.

## Known remaining trait-typed sites (not on the guest path)

`src/app/simpleos_gpu_host/platform_contract.spl:25` and its two
implementations return `Result<DrawIrRenderTarget, text>`. That lane is
genuinely polymorphic (macOS returns `MetalDrawIrRenderTarget`, others return
`Engine2D`), so it cannot simply be retyped. It carries the same latent trap in
native builds and is tracked here.

## Ruled out

- `index_of_builtin=2305843009213693951` (= `2^61-1`, a real tag-box/ABI leak in
  the `payload()` logical-shift untagger,
  `src/compiler_rust/runtime/src/value/core.rs:176`) is emitted at
  `simple_web_html_layout_renderer_foundation.spl:773`. The value is a loop-local
  `val` used only in a `!=` comparison and a `print`; the actual scan uses
  `find_from`. It never selects a dispatch target. **Not the cause.**
- `[web-style-producer] budget-break at=2 of=11`
  (`simple_web_html_layout_renderer_core.spl:1785`) is a pure wall-clock
  deadline (`WEB_RENDER_BUDGET_MS`), shares no data with the above, and is an
  independent perf issue. **Not the cause.**


## 2026-08-17 CORE-P1 triage: STILL PRESENT in current source

Re-verified against CURRENT SOURCE during the crit_01 CORE-P1 sweep. Confirmed still present. A vtable is written only when `vtable_data_id` is present (`src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs:351-355`, stored at object offset 0), and that is driven by a recorded `impl Trait for Type`; a bare `class X with Trait` declaration alone does not populate it. The call then hits `closures_structs.rs:2302`, whose own comment reads "duck-typed virtual method call (trait has no `impl Trait for ...` in unit; no vtable)", and lowers to `builder.ins().trap(...)` -- which is the `ud2` this doc decoded from `rip` (`0f 0b`). The trap is deliberate and fail-closed; the missing piece is real trait-receiver dispatch.\n\n**ROOT-CAUSE COLLAPSE: same single defect as `jit_game2d_backend_method_dispatch_sigsegv_2026-07-02.md`** -- same sentinel (`DUCK_DISPATCH_UNSUPPORTED_SLOT`, `mir/lower/lowering_core.rs:1137-1142`), same trap site. Two P1 docs, one fix.
