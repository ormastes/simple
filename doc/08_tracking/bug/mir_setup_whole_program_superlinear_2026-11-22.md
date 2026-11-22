# Whole-program bootstrap MIR: hours of silent lowering reported as `mir_setup:physical_owners`

**Date:** 2026-11-22 · **Branch:** release/1.0.0 · **Compiler:** admitted Stage 2 built from `0d8a3269bec`
**Status:** open. Mislabelling fixed in source; the slowdown itself is measured but not located.

## Symptom

`native-build --entry-closure --mode dynload --backend llvm` of the bootstrap
CLI (1601 modules) with `SIMPLE_BOOTSTRAP=1 SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1`.
HIR finished with zero errors at about 33 min. The last progress row was

```
[build] phase=mir ... done=0 total=1601 ... elapsed_ms=2007257 current=mir_setup:physical_owners
```

followed by the bootstrap-flat warning and one `TextSpan re-registered`
warning. The worker then ran on one core for more than two hours with no
output. Worker RSS went from 16.6 GB (02:04) to 25.3 GB (03:55), in steps:
+4 GB in 18 min at 03:04-03:22, +0.3 GB in 24 min at 03:28-03:52
(`~/.simple/prov/p3wp/rss.trail`).

## What actually runs under that label

`mir_setup:physical_owners` is the last row the whole-program lane shares with
the direct lane. With `SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1` and
`app.cli.bootstrap_main` in the sources, `lower_to_mir`
(`src/compiler/80.driver/driver_pipeline_lowering.spl`) enters the
bootstrap-fixed branch and returns from it. The direct lane's
`mir_setup:struct_prescan`, `enum_inventory` and `composite_inventory` rows and
its `[mir] i/N` line are never reached. In order, the branch runs:

1. `mir_provider_session_content_key_v1` once: 1601 name/path rows, one SHA-256.
2. struct prescan, `prescan_module_struct_names` per source: linear in the
   3,099 struct/class/enum declarations. No transient scope. This is where the
   `TextSpan` warning is printed.
3. `register_module_enum_bootstrap_inventory_v1` and
   `register_module_composite_inventory_v1` over all modules: linear in
   declarations.
4. `lower_bootstrap_closure_module` for each of the 1600 non-entry modules,
   then `lower_bootstrap_entry_module`.

Every message in steps 2-4 went through `log_phase`, which prints only under
`SIMPLE_COMPILER_PHASE_PROFILE=1` or `SIMPLE_COMPILER_TRACE=1`. So the two
silent hours are step 4, the lowering of the whole closure, not setup.

## Measurement: the same binary, the same closure, the other lane

The direct lane (no `SIMPLE_BOOTSTRAP_WHOLE_PROGRAM`) on the same Stage 2 and
the same 1601 modules, from `~/.simple/prov/p3/build.log`:

```
[mir] 50/1601 rss_mib=14393 elapsed_s=202
[mir] 1601/1601 rss_mib=16994 elapsed_s=1900
```

A second run of that lane took 1689 s. That is about 1.1 s per module and
+2.6 GB for the whole phase, setup included. The whole-program lane had used
more than 7,000 s and +8.7 GB when this was written and had not finished: at
least 3.7 times the direct lane's wall time and 3.3 times its retained memory.

## Suspects, by estimated operation count (n = 1601 modules)

Counted in the closure's sources: 25,238 functions, 3,099 composites and enums,
4,156 module constants, 1,537 externs, 48 traits in 34 modules, 56 trait impls
in 28 modules (952 functions in those 28).

| step, per consumer module | work | total |
|---|---|---|
| promotion walk (`promote_transient_owner`, about 280 roots, one share window) | whole owner graph, including the provider session index over 25k functions | n x graph; at 1M nodes, 1.6e9 node visits |
| native trait declarations and implementations | 48 trait layouts, a 952-row function index, 56 impls, about 1,500 type relocations | 2.4e6 relocations |
| `record_imported_exact_extern_modules_with_context_v1` | every consumer symbol plus 1601 provider probes | 2.6e6 probes |
| `remember_provider_module_default_constants_v1`, provider loop, `ensure_provider_session_v1` check | 1601 dict probes each | 7.7e6 probes |
| `promote_legacy` of the flat store (no build session) | `callable_link_names`, `callable_text_value_abi`, `function_value_names`, about 1e5 nodes | 1.6e8 node visits |

Every row also runs in the direct lane, which finishes in 1,900 s, so none of
them alone explains the difference. What only this lane does:

- lowers through `lower_module`'s bootstrap-flat branch (`ambient_bootstrap_enabled()`),
  with the flat `_bootstrap_mir_*` / `_bootstrap_fn_*` registries and their
  per-module promotion;
- keeps `trait_impl_provider_modules` set to the whole closure feed;
- runs its prepass without a transient scope;
- reports a refused transient scope only on stderr, which the worker relay
  drops. A refused scope lowers the module unscoped and retains its arena
  (about 36 MB per module measured on 2026-10-20). The RSS steps above fit
  that, but nothing in the log confirms it.

The step that costs the hours is step 4 as a whole. Which part of it is not
established: attaching to the live build was not allowed, and the lane printed
nothing.

## Avoiding it on the `0d8a3269bec` binary

- Leave `SIMPLE_BOOTSTRAP_WHOLE_PROGRAM` unset. The direct per-module lane
  lowers the same closure in 1,689-1,900 s on this binary.
- To keep the lane and see it: `SIMPLE_COMPILER_PHASE_PROFILE=1` prints one
  `aot:bootstrap_fixed:closure_module module=...` line per module, and
  `SIMPLE_PHASE_RSS=1` adds RSS to each. `SIMPLE_MIR_SECTION_PROFILE_FILE=<file>`
  splits each module into the `p0`..`p7`, `s1`..`s5` sections.

## Change

`driver_pipeline_lowering.spl`, bootstrap-fixed branch only: three
`log_build_progress` rows (`mir:bootstrap_fixed:struct_prescan`,
`:inventories`, `:closure_modules`) and the direct lane's
`[mir] i/N rss_mib=... elapsed_s=... module=...` line every 50 modules. No
lowering behaviour changes. No spec: the branch is reachable only through a
full driver run, and no compiler could be run while the build was live.

## Next step

Run the lane once with `SIMPLE_MIR_SECTION_PROFILE_FILE` set and compare the
per-section deltas against the direct lane. Check the worker's stderr for
`[mir-scope] WARNING transient scope refused`.
