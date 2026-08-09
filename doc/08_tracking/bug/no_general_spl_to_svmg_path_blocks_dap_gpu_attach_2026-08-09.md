# No general `.spl` → SVM-G path: DAP GPU attach is routing-only

**Status:** OPEN — architectural gap, not a defect in any landed stream

**Re-confirmed 2026-08-09:** verified by reading this doc in full. It already
states plainly that this is an architectural gap, not a defect in any landed
stream, with `lower_svmg_program` existing but scoped to test bodies only and
having no callers outside `70.backend`. Confirmed accurate; no contradicting
evidence found. Left OPEN as characterized — decision on (a) widen + wire vs.
(b) drop the `.spl`-attach expectation is still pending and out of scope for a
point fix.
**Found:** 2026-08-09 by stream P9 (target-neutral DAP session); scope corrected
by the coordinator on inspection
**Component:** `src/compiler/70.backend/svmg_lowering.spl`, `src/app/dap/target_session.spl`

## The gap

P9 landed a DAP session that drives any `DebugTarget`. GPU **mode resolution**
works end to end, but there is **no DAP attach path to a GPU `DebugTarget`**: the
P6/P6b CUDA and Vulkan sessions attach SVM-G *assembly* plus a kernel artifact,
and a user debugging a `.spl` file has neither.

P9 recorded this in-file as `TODO(P9-gpu-attach)` and made the session report the
limitation verbatim and **refuse to fall back to the host** — the right call: a
silent host fallback would look like GPU debugging that mysteriously never hits
a device.

## Correcting P9's statement of the cause

P9 wrote that "no `.spl` → SVM-G lowering exists". That is imprecise. A lowering
module **does** exist — `src/compiler/70.backend/svmg_lowering.spl`, with
`pub fn lower_svmg_program(main_body: HirBlock, helpers: [SvmgHelperFn],
step_budget: i64) -> LoweredProgram`, and a green 17/17 spec
(`svmg_lowering_spec`). Two things are true instead:

1. **Its scope is narrow.** Its own docstring: *"Lower a checked HIR **test
   body** (plus any non-recursive helper fns it calls)"*. It is not a general
   `.spl` lowering — recursion is excluded, and the entry shape is a test body,
   not an arbitrary module.
2. **It has no callers outside its own layer.** `grep` for
   `svmg_lowering` / `lower_svmg_program` across `src/` returns nothing outside
   `70.backend`.

So the operational conclusion P9 reached is correct, and the remedy is larger
than "write a lowering": it is *widen the existing lowering's scope* **and**
*wire it into a callable path*.

## Pattern worth noting

This is the third "implemented but wired to nothing" mechanism found in this
codebase, alongside:

- `desugar_traits` (`src/app/desugar/`) — trait-group `with` sugar, zero callers
  in any compile path, so the landed sugar is inert
  (`trait_group_with_sugar_unwired_and_from_aot_if_val_2026-08-09.md`).
- `action_key.spl` / `interface_digest_of` — deliberately compute-and-log only,
  documented as such, with no `ActionDep` construction site to integrate into.

A green spec proves the module works in isolation; it says nothing about whether
any production path reaches it. When claiming a capability exists, check for a
caller, not just an implementation and a passing test.

## Next step

Decide the intended shape before building: either (a) widen `lower_svmg_program`
to general `.spl` and wire it into the GPU attach path, or (b) keep GPU debugging
scoped to explicitly-authored SVM-G programs and drop the `.spl`-attach
expectation from the design. (b) is much cheaper and may be the honest scope —
the notebook/Lab lanes already work with SVM-G sources directly.
