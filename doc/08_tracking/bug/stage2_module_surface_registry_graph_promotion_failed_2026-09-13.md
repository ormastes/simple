# Stage 2 passes sanity and the struct receiver, then fails the Stage-3 route in `module_surfaces_promote`

- Status: **FIXED (2026-09-13, proven by BOOT-7)** — `592041db98a` removes the
  repeat-promote post-condition from `module_surface_promote_freeze_names`. The proof is
  `build/bootstrap-boot7b` (candidate sha256 `f02b5a4c1310df6e...`, 152198856 B): the
  message below appears nowhere in that run, and the positional Stage-3 route advances six
  phases further — through `parse`, `hir`, `monomorphize`, `mir` and `native_cache` — before
  hitting an unrelated SEGV tracked as site 8
  (`stage2_stage3_route_segv_mir_json_shadow_witness_2026-09-13.md`)
- Found: bootstrap lane BOOT-7, `work/bootstrap-full-5-2026-09-12` at `823da06e9fa`
- Severity: **the current `--stop-after-stage2` admission blocker on Linux aarch64**, and the
  successor to site 6 (`stage2_positional_stage3_route_scv_authority_missing_2026-09-13.md`,
  now CLOSED). Like site 6 and unlike sites 1-5 this is not a compile defect: the compiler
  compiles, links, passes both sanity passes and the struct-receiver probe.

## The verdict, verbatim

`build/bootstrap-boot7a/stage3/aarch64-unknown-linux-gnu/stage2-receiver.log`:

```
bootstrap_stage2_struct_receiver=PASS
error: stage2 failed the positional pure-Simple Stage-3 route (status 1)
...
phase2:surface:file:released path=scripts/check/cert/redeploy_gate/fixtures/stage2_module_path_naming.spl seq=1
...
phase2:surface:file:released path=src/compiler/common/module_path_naming.spl seq=2
[ERROR] phase 2 FAILED (1 recorded error(s))
[ERROR]   Module surface registry graph promotion failed after phase 2
[build] phase=parse state=failed unit_kind=files done=unknown total=2 remaining=unknown succeeded=unknown cached=0 failed=1 task_done=1 task_total=6 elapsed_ms=13005 dt_ms=12605 current=failed
error: in-process native-build: Module surface registry graph promotion failed after phase 2
```

Both files parse, surface, promote, commit and release cleanly (seq=1, seq=2). The failure is
strictly after that, in the registry-level graph promotion.

## Reproduced outside the harness, deterministically

`scratchpad/boot7/probe7.sh` replays
`scripts/check/check-bootstrap-stage2-struct-receiver.shs:134-166` against the preserved
candidate (sha256 `3ad6fc2a0ac80727...`, 152199192 B):

| probe | env | rc | outcome |
|---|---|---|---|
| `streaming` | `SIMPLE_STAGE3_STREAMING_SURFACES=1` (what the gate sets) | **1** | the three lines above, byte for byte |
| `nostream` | `SIMPLE_STAGE3_STREAMING_SURFACES=0` | **139** | SIGSEGV — the non-streaming path is worse, not a workaround. Filed separately. |

## Where it comes from

`src/compiler/80.driver/driver_source_pipeline_parsing.spl:585-587` raises the message when
`module_surfaces_promote(retained_surfaces)` answers false.
`src/compiler/20.hir/hir_lowering/module_surface_registry.spl:344-382` has exactly three
ways to answer false, and the message names none of them — the same "does not say which"
defect site 6's record called out:

1. one of 24 `rt_transient_heap_promote(surface.<field>)` calls in the per-surface chain;
2. `module_surface_promote_freeze_names(surface)`;
3. the tail `module_surface_promote_roots(roots)` (i.e. `rt_transient_heap_promote(roots)`).

A static argument worth testing before anything else: `module_surface_promote`
(same file, :310-343) already promotes `composite_names`, `enum_names`, `trait_names`,
`callable_names`, `type_alias_names`, `constant_names`, `import_item_*`, `callable_values`,
`composite_values`, `enum_values`, `trait_values`, `type_alias_values`, `constant_values`
in the PER-FILE scope. `module_surfaces_promote` then calls `rt_transient_heap_promote` on
those same fields again. `module_surface_promote_freeze_names`'s own docstring states that a
value which is ALREADY persistent answers **false** and that this is not an error — if that
is true of arrays too, the 24-way chain cannot pass for any surface that went through
`module_surface_promote`. MEASURE this (the field index of the first false), do not assume it.

## Not yet measured

- which of the three sites answers false, and for which field/surface;
- whether `rt_transient_heap_promote` can also answer false for allocation failure, which
  would change the fix shape.

## What the removed guard was, and was not, worth

Two things, stated because "a fail-closed check was deleted" deserves them:

1. **It could never catch a genuine promotion failure.** A value whose FIRST promote answers
   false (the docstring's own "already persistent" case) also answers false on the second, so
   it passes the guard. The only thing the guard could distinguish was a value whose repeat
   promote answers TRUE — which, measured above, is every raw/array/dict/enum/closure
   representation whether or not the promotion worked. It fired on success and stayed silent
   on the failure it was written for.
2. **The remaining check is not an equivalent substitute, and is not claimed to be.**
   `module_surfaces_frozen_alignment_error` (`module_surface_registry_index.spl:321`) runs
   AFTER `_sffi_transient_array_scope_end()` and reads `preferred_registry_name` back out of
   the dead scope — a real post-scope-end read at the only moment such a read means anything.
   But it tests `== ""`, so it catches an emptied name, not a dangling pointer into freed
   memory reading as garbage, which is the shape the 2026-09-06 SEGV had. Coverage of the
   four freeze-assigned names after scope end is therefore PARTIAL, not restored.
