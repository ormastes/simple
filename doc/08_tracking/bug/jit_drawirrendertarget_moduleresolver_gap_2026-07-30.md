# JIT `Unknown type: DrawIrRenderTarget` — confirmed reproduction, root-caused, fix attempted and reverted (unverified), architectural blocker identified

**Date:** 2026-07-30
**Status:** OPEN — reproduction and root-cause analysis are solid (PROVED); a
mirrored fix was implemented, built, and validated as safe, but could not be
proven to fix anything and was reverted rather than landed unverified. The
actual blocker for the assigned repro is a second, architecturally separate
JIT entry point with no cross-module type-fallback infrastructure at all.
**Component:** `src/compiler_rust/driver/src/exec_core.rs` (`run_file_jit`),
`src/compiler_rust/compiler/src/module_resolver/*`,
`src/compiler_rust/compiler/src/hir/lower/type_registration.rs` (`register_trait`),
`src/compiler_rust/compiler/src/hir/lower/type_resolver.rs` (`resolve_type`)

## Reproduction (PROVED, from a pristine worktree)

Per the coordinator's correction on the sibling `ot_layout_shaper.spl` doc
(the shared WC was contaminated by another session; this investigation was
redone from a fresh `git worktree add --detach` at the SSH-fetched origin
tip, never the shared WC):

```
SIMPLE_EXECUTION_MODE=jit SHOWCASE_RESOLUTION=480x360 \
bin/release/x86_64-unknown-linux-gnu/simple run examples/06_io/ui/web_render_file_gui.spl
```

```
[INFO] JIT compilation failed, falling back to interpreter: HIR lowering error: Unknown type: DrawIrRenderTarget
```

This confirms the `web_style_producer_4s_per_node_interpreted_lane_2026-07-29.md`
finding is accurate and current — `DrawIrRenderTarget` genuinely is the
first blocker forcing JIT hits, from a pristine checkout, today.

`DrawIrRenderTarget` is a **trait**, not a plain class/struct (`trait
DrawIrRenderTarget:`, `src/lib/gc_async_mut/gpu/engine2d/draw_ir_target.spl:28`),
implemented by `Engine2D` (`engine.spl:181`) and `MetalDrawIrRenderTarget`
(`draw_ir_target_metal.spl:32`).

## Root cause (PROVED by code reading) — a real, confirmed asymmetry

`register_trait` (`type_registration.rs:446-483`) registers a trait's name
as a `TypeId::ANY` alias (`self.module.types.register_alias(t.name.clone(),
TypeId::ANY)`, line 480) — but **only in the local type table of the module
that defines the trait** (`self.module.types`, per-`Lowerer`-instance state).

`resolve_type` (`type_resolver.rs:113-247`), when a type name isn't found in
the current module's own table (`self.module.types.lookup(name)`, line 138),
has an explicit **cross-module fallback for struct names** (lines 144-168,
`self.global_struct_defs`) — "This handles files that use a struct type by
name... without an explicit `use` statement." **There is no equivalent
fallback for trait names.** A module that references a trait as a type (a
parameter annotation, a return type) without itself running `register_trait`
for it locally (i.e. without itself implementing/declaring that trait) falls
through every branch to the final `UnknownType` error — exactly the observed
symptom, and exactly the class of gap `global_struct_defs` was built to
close for structs.

This asymmetry is a real, confirmed, precisely-located gap in
`compile_file_to_object`'s pipeline (`native_project/compiler.rs`,
`hir/lower/*`) — but see "Why not fixed" below for why it turned out not to
be the operative blocker for the assigned repro.

## Fix attempted, validated safe, but reverted — unverified necessity

Implemented a mirror of the existing `global_struct_defs` mechanism for
traits: added `trait_defs: HashSet<String>` alongside `struct_defs` in
`ImportMapResult` (`imports.rs`, populated for free — `trait_def_names` was
**already being collected** during the same discovery walk, just never
exposed), threaded it through `ModuleImports` (`mod.rs`) and
`compiler.rs`'s existing `imports.populate_global_struct_defs` gate, added
`global_trait_defs`/`set_global_trait_defs`/`global_trait_defs()` to
`Lowerer` (`lowerer.rs`, mirroring `global_struct_defs` exactly), and
consulted it in `resolve_type`'s fallback chain (`type_resolver.rs`,
registering `TypeId::ANY` on hit — the same choice `register_trait` itself
makes locally).

**Validation (PROVED):**
- `cargo build --release`: clean, same 16 pre-existing warnings, zero new,
  none in the 6 touched files.
- `rustfmt --check` on all 6 touched files: clean, zero diffs.
- Byte-identical-archive check on an unaffected fixture (old seed vs.
  patched seed, `check4_test.spl`, `--entry-closure --emit-archive --target
  x86_64-unknown-none --backend cranelift`): sha256-identical
  (`a6994edb73067fdd16041e1e41db89e156f4a84029c9658e3a1a01b9a0aca202`, both
  builds) — zero collateral codegen change.

**But: could not construct a positive-proof test.** A fixture built to
exercise exactly this gap (`fn touch(target: DrawIrRenderTarget)` in a file
that imports `Engine2D`, i.e. `class Engine2D with DrawIrRenderTarget:`,
without itself declaring/implementing the trait) compiled successfully
under **both** the old (unpatched) and new (patched) seed via
`native-build --entry-closure` — meaning either that fixture doesn't
actually trigger the gap the fix targets (the `native_project::compiler.rs`
pipeline may already resolve this case through some other path not
identified this pass), or the gap this fix closes was already unreachable
in that pipeline. **Most importantly: re-running the actual assigned
reproduction command (`simple run --jit` on the web example) with the
patched seed showed the identical, unchanged error** — the fix had no
effect on the actual failing path.

**Given the fix could not be shown to do anything (no failing-before/passing-
after pair found, and it did not move the assigned repro), it was reverted**
(`git checkout --` on all 6 touched files) rather than landed unverified —
per the project's "never add unused code" rule and this session's own
established validate-before-land discipline. The asymmetry itself
(struct fallback exists, trait fallback doesn't) remains real and worth
someone eventually closing, but the revert reflects that this specific
implementation's necessity/correctness was not established.

## Why not fixed — the real, architectural blocker (PROVED)

`simple run --jit`'s actual code path (`exec_core.rs::run_file_jit`, ~line
676) does **not** go through `native_project::compiler.rs` /
`build_import_map` / the `ModuleImports` struct at all. It calls
`hir::lower_with_context_and_project_hint` (`hir/lower/mod.rs:131-140`),
which constructs `Lowerer::with_module_resolver(...)` directly — **no call
to `set_global_struct_defs` or (the now-reverted) `set_global_trait_defs`
anywhere in this path.** Cross-module type resolution here relies entirely
on `ModuleResolver` (`src/compiler_rust/compiler/src/module_resolver/*`), a
different, presumably on-demand/lazy per-import mechanism — **confirmed
(PROVED, grep) to have zero references to `TraitDef` or `register_trait`
anywhere in its four source files** (`manifest.rs`, `mod.rs`,
`resolution.rs`, `types.rs`, `var_overlay.rs`). This is a **second, wholly
separate lowering/JIT pipeline** from the one `native-build`/`compile` use,
with no whole-program cross-module type-fallback infrastructure of its own
— not just missing trait support, but architecturally distinct from where
the (reverted) fix was implemented.

This is exactly the kind of gap that is "architectural" per this task's own
instruction 5: closing it requires understanding and extending
`ModuleResolver`'s on-demand type-loading mechanism (a different subsystem
with different data flow than the whole-program pre-scan `build_import_map`
performs), not a small mirrored addition. Not attempted this pass — no time
remained to safely trace and verify a fix in unfamiliar territory.

## CastElse gap — not reached this pass

The second documented gap (`Unsupported feature: CastElse` on `read_u32_be`
in `src/lib/skia/feature/glyph/ot_parser_layout.spl:280`) was not
independently re-investigated this pass — time was consumed by the
`DrawIrRenderTarget` root-cause/fix/revert cycle and the architectural
discovery above. Given both gaps are reached via the same
`exec_core.rs::run_file_jit` → `ModuleResolver` path, and `DrawIrRenderTarget`
is hit first (blocking further progress on the real pipeline), it's likely
`CastElse` is architecturally similar (a genuinely unsupported HIR node in
this same simpler lowering path) but this is **INFERRED, not verified**.

## Recommended next steps

1. Understand `ModuleResolver`'s on-demand type-loading path well enough to
   add trait-name (and, generalizing, any other missing) fallback support
   there specifically — the `native_project` pipeline's `global_struct_defs`/
   (reverted) `global_trait_defs` mechanism is not directly reusable since
   `run_file_jit` never builds a whole-program `ModuleImports` map at all.
2. Once `DrawIrRenderTarget` is cleared via a `ModuleResolver`-side fix,
   re-run the same `SIMPLE_EXECUTION_MODE=jit` repro to see whether
   `CastElse` on `read_u32_be` (`ot_parser_layout.spl:280`) is the next
   blocker, confirming or revising the "architecturally similar" inference
   above.
3. If closing `ModuleResolver`'s gap is itself large, consider instead
   routing `simple run --jit` through the same whole-program
   `native_project::compiler.rs` pipeline `native-build` uses (which does
   have the struct fallback, and could gain the trait one) — a bigger
   change, but reuses solid, already-tested infrastructure instead of
   duplicating it in `ModuleResolver`.

## Validation performed this pass

- Reproduction: PROVED, pristine worktree, exact assigned command.
- Root cause (struct-vs-trait fallback asymmetry): PROVED by code reading.
- Fix: implemented, cargo-build-clean, rustfmt-clean, byte-identical on an
  unaffected fixture — all PROVED — but necessity/correctness NOT proved
  (no failing-before/passing-after pair found), and it did not move the
  assigned repro. Reverted.
- Architectural blocker (`ModuleResolver` has no cross-module type-fallback
  of any kind, trait or otherwise): PROVED by code reading (grep across all
  `module_resolver/*.rs` files, zero trait references).
- CastElse gap: not investigated this pass — INFERRED only that it's likely
  architecturally similar.
