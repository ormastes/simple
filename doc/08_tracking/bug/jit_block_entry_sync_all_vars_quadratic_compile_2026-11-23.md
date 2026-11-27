# Seed JIT: block-entry variable sync is O(vars x blocks); the catalog spends ~9.5 s compiling

- **Date:** 2026-11-23
- **Severity:** P2 (performance: under `SIMPLE_EXECUTION_MODE=jit` every web catalog
  run spends ~9.5 s in `compile_all`, more than the interpreter needs for the
  whole tab-bar page)
- **Status:** FIXED 2026-11-23 (seed `codegen/instr/body.rs`, `mir/function.rs`,
  `codegen/common_backend.rs`)
- **Area:** `src/compiler_rust/compiler/src/codegen/instr/body.rs`

## Symptom

On the tab-bar page, `SIMPLE_JIT_STAGE_TRACE=1` showed `compile_all` taking
~9.5 s for 4,299 functions, while rendering itself took 0.06 s. Two functions
accounted for 3.9 s of that:

| function | vars | blocks | translate | define |
|---|---|---|---|---|
| `layout_with_style_flow` | 2,212 | 3,134 | 1.35 s | 0.35 s |
| `_apply_decls_without_grid_inner` | 2,412 | 3,174 | 1.22 s | 0.85 s |

Here "translate" is MIR -> CLIF (`compile_function_body`). Across all
functions, translate took 3.83 s and Cranelift `define_function` took 3.98 s.

## Root cause

At the entry of every block, `sync_vars_to_vregs` called `use_var` for every
cross-block vreg Variable of the function, not just the ones the block needs.
All blocks are sealed only after the whole function has been translated. A
`use_var` on an unsealed block adds a block parameter, so each such function
paid vars x blocks: SSA resolution at seal time took ~1 s each, and register
allocation then worked on the inflated block parameters.

A source shape that triggers it is a long run of if-expressions, each merging
its arms through a short-lived vreg:

```simple
s = s + (if x > 0: x * 0 else: 0 - x)
s = s + (if x > 1: x * 1 else: 1 - x)
...
```

## Fix

1. `sync_vars_to_vregs` re-reads only the block's LIVE-IN vregs, from
   `MirFunction::compute_live_ins` (computed once). It also drops every other
   cross-block value from `vreg_values`: such a value belongs to the
   previously translated block, and the terminator sync would otherwise write
   it back into the Variable. A first prototype that skipped this drop failed
   the verifier ("uses value from non-dominating inst") in 3 functions.
2. `compute_live_ins` visits blocks last-to-first. This is a backward problem,
   so a value live across a long chain now converges in one pass instead of
   one pass per block. The fixed point is unchanged.
3. The JIT no longer runs Cranelift's internal verifier (`enable_verifier`,
   which repeats after passes inside `define_function`; ~0.7 s).
   `compile_function` already verified the translated IR once, but only logged
   errors; it now fails closed, returning the same `Verifier errors` error that
   `define_function` used to return. The AOT settings keep the internal
   verifier on (`BackendSettings::verifier`).

Checked with `SIMPLE_STRICT_VREG=1`, which panics on any read of a missing
vreg value, over all 9,021 unpruned functions of the tab-bar program
(`SIMPLE_JIT_NO_REACH_PRUNE=1`): 0 missing reads, 0 verifier errors, and the
same output as with the old sync.

## Evidence

`src/compiler_rust/compiler/tests/jit_block_entry_sync_scales.rs` compiles 300
and then 600 if-expressions and compares the times:

| tree | n=300 | n=600 | ratio |
|---|---|---|---|
| base `7f5cb7077f0` | 0.53 s | 3.69 s | 6.8–7.0 (FAIL) |
| fixed | 0.030 s | 0.097 s | ~3.2 (pass, threshold 5) |

Both trees compute correct values, including a loop-header case.

Catalog timings are in the lane report and in the wiki section dated
2026-11-23 (JIT startup).

## Remaining startup budget (tab-bar, after the fix)

| phase | time |
|---|---|
| load + parse of the import closure | 0.36 s |
| HIR lowering (9,021 functions) | 0.85 s |
| MIR lowering | 0.50 s |
| translate (MIR -> CLIF), 4,299 functions after pruning | ~1.55 s |
| explicit verify | ~0.15 s |
| Cranelift define | ~2.1 s |
| render | 0.06 s |

The interpreter renders tab-bar in about 4.9 s.

At least 2.10 s of the ~3.6 s of codegen (2,862 of 4,299 functions) is never
called on tab-bar. This was estimated by matching interpreter call-trace names
(`SIMPLE_INTERPRETER_CALL_TRACE=1`) against compiled-function base names. The
match over-counts "called", so the uncalled figure is a lower bound. Most of the
uncalled code is the Vulkan / SPIR-V / Metal / DXVK backends (`spirv_*`,
`VulkanBackend.*`, `metal_sffi_*`). They are reachable because the 2D backend
is chosen at run time (`SIMPLE_2D_BACKEND`), so reachability pruning cannot
drop them.

### Designs (not implemented in this lane)

1. **Lazy compile-on-first-call.** For each function `F`:
   - define a small stub `F` that loads `__lazy_slot_F`;
   - if the slot is non-null, the stub `call_indirect`s it;
   - otherwise it first calls `rt_jit_lazy_resolve(id)`, which translates and
     defines the real body `F$body` in the same `JITModule`, runs
     `finalize_definitions` again, and stores the address in the slot.

   Costs and constraints:
   - every call pays a load, a branch and an indirect call (hot pixel loops);
   - the resolver must be re-entrant: a body that calls a cold callee resolves
     it during finalization;
   - it must be thread-safe under parallel render;
   - on aarch64 (`is_pic=false`), bodies allocated later are still reached by
     direct `BL` relocations, so they are exposed to the existing +/-128 MB
     range abort (`jit_aarch64_branch_relocation_out_of_range_abort_2026-09-05.md`).

   Expected saving: about 2 s of tab-bar startup.
2. **Parallel Cranelift codegen.** Keep translation serial: it needs
   `&mut JITModule` to declare func refs. Run `Context::compile(isa)` for the
   translated functions on a worker pool, using message passing rather than
   locks, then `define_function_bytes` with the relocations on the main
   thread. This does not slow down any call site. Expected saving: most of the
   ~2.1 s define phase.
3. **Prune before HIR lowering.** 9,021 functions are lowered to HIR and MIR,
   and pruning keeps only 4,305. An AST-level call-name reachability pass, with
   the same key-matching soundness rule as `mir/reachability.rs`, would cut
   part of the 1.35 s spent in HIR+MIR.
