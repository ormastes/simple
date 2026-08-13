# Same-named traits/structs from different modules collide in the seed's flat registries

- **ID:** seed_flat_namespace_trait_struct_collision_2026-08-09
- **Status:** FIXED 2026-08-09 (seed interpreter + HIR lowerer)
- **Found by:** computer-use 3D/web/2D showcase sweep, 2026-08-09
- **Severity:** high — `check-game3d-rollball.shs` could not even compile its
  driver; GUI showcase runs silently dropped whole modules to the
  interpreter (~100-1000x slowdown, window never appeared within 560s)

## Symptom 1: trait conformance checked against the wrong trait

`SIMPLE_BIN=<seed> sh scripts/check/check-game3d-rollball.shs` failed at
semantic time:

```
error: semantic: type `VulkanBackend3D` does not implement required method
`capabilities` from trait `RenderBackend3D`; ... implements method
`create_pipeline` ... with 4 parameter(s), but the trait declares 1; ...
```

Two different modules declare a trait named `RenderBackend3D`:

- `std.gpu.engine3d.backend` (gc_async_mut facade trait — the one
  `gc .../backend_vulkan.spl` imports and implements)
- `std.nogc_sync_mut.engine.render.backend3d` (low-level handle trait with
  `capabilities`, `create_vertex_buffer`, ...)

`src/app/game.rollball/game.spl` imports both `Engine3D` and
`VulkanBackend3D`; `engine.spl` -> `vulkan_font_adapter.spl` legitimately
imports the nogc trait too, so both traits land in one compilation.

### Root cause 1

`src/compiler_rust/compiler/src/interpreter/core_types.rs`:
`type Traits = HashMap<String, TraitDef>` — the interpreter flattens every
imported module into one namespace, so the second registration of a
same-named trait overwrote the first, and impl-block conformance
(`interpreter_eval.rs`) checked `VulkanBackend3D` against whichever trait
survived.

### Fix 1

`Traits` is now `HashMap<String, Vec<TraitDef>>`; registration pushes every
candidate, and the impl check accepts the impl when it fully conforms to ANY
same-named candidate (reporting the closest candidate's problems when none
matches). Contained to `core_types.rs` + `interpreter_eval.rs` (the only two
use sites).

## Symptom 2: HIR `Cannot infer field type` drops the GUI module to the interpreter

`main_gui.spl` (ui_showcase GUI host) JIT-lowering failed with:

```
[jit-fallback] HIR lowering error: Cannot infer field type: struct
'GlyphBitmap' field 'gbm_width' [in src/app/ui_showcase/hosts/main_gui.spl]:
whole module dropped to the interpreter (expect ~100-1000x slowdown)
```

Three modules declare `class GlyphBitmap` (`skia/feature/glyph/rasterize.spl`,
`nogc_sync_mut/io/font_sffi.spl`, `nogc_sync_mut/sffi/spl_fonts.spl`); only
the `spl_fonts` one has the `gbm_*` fields. The nominal-owner field lookup
resolved `GlyphBitmap` to a variant without `gbm_width`, and
`try_resolve_global_field_for_struct`
(`src/compiler_rust/compiler/src/hir/lower/type_resolver.rs`) had a
`has_nominal_owner` early-return that vetoed the duplicate-variant consensus
scan whenever a nominal owner existed — even when the owner's layout lacked
the field entirely.

### Fix 2

Removed the `has_nominal_owner` veto: when the nominal owner's fields lack
the name, the duplicate-variant consensus scan now runs (it resolves only
when every variant declaring the field agrees on its index — still
fail-closed for genuinely ambiguous fields). This aligns the get-field path
with the existing `resolve_duplicate_global_field_variant` set-field path.

## Verification

- Rebuilt seed: `cargo build --locked --offline --profile bootstrap
  -p simple-driver` (rust-authority dir), deployed to
  `src/compiler_rust/target/bootstrap/simple`.
- `check-game3d-rollball.shs` with the fixed seed: `overall=pass`
  (SESSION/WINSTATE/LOSESTATE/DISTINCT/MOTION/OCCLUSION/CAMERA/VULKAN/HUD
  all PASS; fresh PPM evidence under `build/game3d-rollball/`).
- Known remaining note: the pure-Simple compiler likely carries the same
  flat-registry assumptions; the self-hosted redeploy is blocked separately
  by the in-flight `bootstrap_linux_repair` lane
  (`.spipe/bootstrap_linux_repair/state.md`), so parity could not be checked
  this session.

## 2026-08-11 run-lane fix (second session)

FIXED for the `run`/JIT lane: `module_loader::collect_duplicate_struct_defs`
now walks the flattened AST and feeds every distinct same-named struct/class
layout to the lowerer (`set_duplicate_global_struct_defs`) via the new
`hir::lower_with_context_lenient_project_hint_and_duplicate_structs` entry,
wired in `run_file_jit` (driver/src/exec_core.rs). The constructor path
(`hir/lower/expr/collections.rs::lower_struct_init_fields`) picks the unique
variant covering every provided named argument when several layouts collide,
so both construction order and the typo gate use the right layout.

Verified: a two-module repro (two `Thing` classes with disjoint fields)
previously de-JITted with `Cannot infer field type: struct 'Thing' field
'alpha'`; it now JIT-compiles under SIMPLE_JIT_STRICT=1 and prints the
correct value. The vk module graph probe (`Engine2DReadback.device_identity`)
also JITs cleanly. No regressions: showcase_core 13/13, named_ctor 4/4,
struct_init 5/7 (2 pre-existing reds identical on the pre-fix seed), builder
42/45 (3 pre-existing reds identical).

Remaining: modules still de-JIT when they create lambdas (closure ABI),
reference unresolved externs (e.g. `subsys_from_scope`), or call vulkan
externs under JIT (init reports unavailable — the JIT extern ABI family).
Those are separate documented classes; the GUI showcase still interprets
because of them.

## 2026-08-11 final state (third session)

- The run-lane feed is now GATED: `run_file_jit` only collects/feeds the
  duplicate-struct map when `SIMPLE_JIT_DUP_STRUCT_FEED=1` is set. Default
  off. Reason: with the feed on, the ui_showcase 2D render JIT-compiles and
  produces a WRONG frame (missing widgets, lost clip groups; 52192/76800 px
  differ from the interpreter-correct capture) — the map only unblocks HIR;
  the JIT then miscompiles this module graph for independent, pre-existing
  reasons (likely the global widget-store semantics class). Fast-but-wrong
  is worse than slow-but-right, so the feed defaults off until the JIT
  correctness gap is fixed.
- `lower_struct_init_fields` variant selection is now coverage-gated: it
  only overrides the registry layout when that layout fails to cover the
  provided named arguments (the hard-error case), never for constructors
  the registry already covers.
- The field-receiver guard (`rt_struct_receiver_valid`, in flight on the
  `codex/runtime-struct-receiver-guard-*` branch) has no seed-linkable
  symbol yet — its C definition lives in runtime_native.c, which the seed
  crate cannot link wholesale. `instr/fields.rs` therefore neutralizes the
  guard unless `SIMPLE_SEED_FIELD_GUARD=1` is set; without this, EVERY JIT
  field access panics (`missing runtime fn 'rt_struct_receiver_valid'`),
  making the seed unusable for `run`. Flip the default once the guard lane
  lands the seed-side symbol.
- A/B on ui_showcase main_2d (320x240, 1 frame): feed off = 2m57s,
  pixel-identical to the interpreter reference; feed on = ~3s but wrong
  frame. Simple two-module collision repro: JITs correctly with feed on.

## 2026-08-09 follow-up (gui/web/2D vulkan sweep): why Fix 2 does not help `simple run`

`main_gui.spl` / `web_standards_showcase_gui.spl` still log the
`GlyphBitmap.gbm_width` "Cannot infer field type" whole-module de-JIT under
the rebuilt seed. Root cause narrowed down: `duplicate_global_struct_defs`
(and `set_global_struct_defs`) are populated ONLY by the AOT pipeline
(`pipeline/native_project/imports.rs` → `compiler.rs:668`). The JIT/`run`
lane (`codegen/jit.rs` via `local_execution.rs`) never sets either registry,
so the consensus-scan fallback in `try_resolve_global_field_for_struct`
always sees `None` there and the Struct-arm lookup still fails closed. A
complete fix needs the run lane to collect the same import struct registry
the AOT lane builds (or an equivalent per-program duplicate-struct map
threaded into the JIT lowerer). Until then `run` on any module whose closure
contains same-named structs with divergent fields silently de-JITs the whole
module (~100-1000x slowdown — observed: GUI showcase window mapped but first
frame not presented after ~30 min interpreted).

## 2026-08-13 Vulkan retained-render follow-up

The canonical lavapipe readback gate again produced exact clear and rectangle
checksums with device-readback provenance, but correctly returned
`native_execution_status=fail` because the JIT fell back to the interpreter.

Two local flat-name collisions in the GC Engine2D session contract were removed
without changing its public compatibility names: the GC-only concrete classes
are now `GcComputeError`, `GcBackendSessionPolicy`, and
`GcBackendSessionHandle`; compatibility aliases retain the documented session
surface. The focused backend-session contract passed. This advanced the gate
from `ComputeError.kind` and `BackendSessionPolicy.allow_interop_present`
lowering failures to the existing `GlyphBitmap.gbm_width` failure.

The remaining `GlyphBitmap` failure is the duplicate-struct JIT feed issue
described above. Do not enable `SIMPLE_JIT_DUP_STRUCT_FEED=1` to claim this
Vulkan lane native: the prior UI-showcase A/B recorded a fast but pixel-wrong
frame with that feed enabled. The gate remains valid interpreter
correctness/readback evidence only, not native Vulkan throughput evidence.
