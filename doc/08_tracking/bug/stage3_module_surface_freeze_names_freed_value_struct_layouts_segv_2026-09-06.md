# Stage 3 SIGSEGV in `value_struct_layouts`: `module_surfaces_freeze` names are freed by the registry retention scope

- **Filed:** 2026-09-06
- **Severity:** P0 — the single blocker to a deployed self-hosted compiler; every
  Stage-3 self-host on aarch64 died here after ~69 minutes of clean HIR lowering.
- **Component:** `src/compiler/20.hir/hir_lowering/module_surface_registry.spl`
  (`module_surfaces_promote`), surfaced by
  `src/compiler/35.semantics/value_struct_layout.spl`.
- **Same defect family as** `phase3_hir_worker_transient_surface_index_segv_2026-08-30.md`
  ("`ModuleSurfacesByName.index_by_name` is a construction-time dictionary owned
  by the transient surface arena") and
  `stage3_surface_freeze_segv_blocks_mcdc_rt_hal_verification_2026-08-25.md`.
  Those rows covered ARRAY and DICT carriers; this row is the four scalar TEXT
  fields nobody enumerated.

## Symptom

`build/bootstrap/logs/aarch64-unknown-linux-gnu/stage3-native-build.log`:

```
[BOOTSTRAP-PHASE] +4162614ms phase3:hir:ctx_publish:done modules=1064 errors=0
[BOOTSTRAP-PHASE] +4162614ms phase3:hir:validate:start keys=771 values=771
[BOOTSTRAP-PHASE] +4162614ms phase3:hir:validate:value_struct_layouts:start
error: native-build worker was KILLED by signal 11 before producing a binary; NOT a compile failure.
```

1,064 modules lowered with zero errors, then a SIGSEGV on entering the
by-value-struct-cycle validator.

## Classification — settled by the core, not by inference

Core: `/var/crash/_home_yoon_bootstrap-wt_..._stage2-admitted_simple.1000.crash`
(39 GB, apport, unpacked to `/home/yoon/segv-lane/unpack/wt1/`). The crashing
process is the `native-build` worker, i.e. the admitted Stage-2 binary
re-invoked as `simple run src/app/cli/native_build_worker.spl` — a native
binary, not the Rust seed.

| candidate | verdict | evidence |
|---|---|---|
| stack overflow | **NO** | `VmStk: 132 kB`; `[stack]` is `fffffde43000-fffffde64000`; `sp` is 3 pages inside it |
| OOM / allocation failure | **NO** | signal 11 not 9; `VmSwap: 0`; 38 GB RSS of 121 GB; the fault address is 0x18, not a failed brk |
| miscompilation of the validator | **NO** | the faulting instruction is exactly what the source says |
| **nil dereference** | **YES** | `si_addr = 0x18`, `x21 = 3` (`RT_VALUE_TAG_SPECIAL` payload 0 = nil) |

Faulting instruction, byte-identical between the core's text pages and the
on-disk binary, so the symbolisation is trustworthy:

```
0x347e8a8 <validate_value_struct_layouts+3316>: and x8, x21, #0xfffffffffffffff8
0x347e8b0 <validate_value_struct_layouts+3324>: ldr x8, [x8, #24]     <-- SIGSEGV
0x347e8b8:                                      bl  <rt_for_iterable>
```

That is `for field in struct_.fields:` with `struct_` nil.

## The chain, read out of the core

1. `x27 = 1`, `[sp+16] = 0` — the crash is the FIRST root of the FIRST pending
   walk, milliseconds after the phase line.
2. `roots` (`[text]`, len 918, buffer `0x1071020f0`): **523 entries are nil (3)**
   and 395 hold a string. So `roots[0]` is nil, `structs[nil]` misses, and the
   nil result is walked.
3. The 395 surviving keys read like
   `"1 12 F |MirPassDescriptor"`, `"71 EvalContext|HashMapEntry"`,
   `"76 BackendKind|InterpreterBackendImpl"` — a correct `struct_.name` after
   the `|`, and **garbage before it**. The garbage is the module key.
4. `module_keys` (arg 0, `[sp+64]`, len 771): every handle is a valid tagged
   pointer, but the string OBJECTS read back as unrelated content —
   `"[hir-reexport-chase-unresolved] facade=compiler.driver.driver_types item=bool ..."`,
   `"ler.hir.hir_definitions dependency=Option"`, `"560 Result"`. **Freed and
   reused**, not nil.
5. Whether a given key comes back as nil or as garbage depends only on what the
   allocator later put in that memory: a slot reused as a non-string object makes
   `module_key + "|" + name` return nil (523 of them); a slot reused as a string
   makes it return garbage (395).

## Root cause

`validation_module_keys` is filled with
`retained_module_surfaces.surfaces[i].logical_name`
(`driver_hir_pipeline_lowering.spl:348` and `:919-920`).

`ModuleSurface.logical_name` is **re-assigned by `module_surfaces_freeze`**
(`module_surface_registry_index.spl:395-398`) together with `canonical_name`,
`package_name` and `preferred_registry_name` — four freshly allocated strings.
Freeze runs via `builder.finish_into(...)` inside the dedicated registry
retention scope opened at `driver_source_pipeline_parsing.spl:538`.

`module_surfaces_promote` then promotes ~24 arrays per surface and the registry
carrier, and finishes with `rt_transient_heap_promote(registry)`. That walk
cannot reach the four strings: the surface's own raw allocation belongs to the
older per-file parse scope, which has already ended, so
`rt_core_transient_classify` does not recognise it and the RAW slot walk over the
surface never happens. The function's own comment already states this ("a graph
walk cannot traverse an old raw allocation that is no longer registered in the
current transient scope") — the arrays were enumerated for exactly that reason,
and the four scalar texts were simply omitted.

`_sffi_transient_array_scope_end()` therefore `free()`s all 771 `logical_name`
strings while every surface still holds the handle. Nothing reads them again for
the next ~69 minutes of HIR lowering — which is why the crash always lands at the
first pass that does, and why the freed storage is thoroughly recycled by then.

Note what did NOT break, because it is the control: `canonical_path` and
`module_name` are set at construction inside the PER-FILE scope, where the
surface IS a scope-owned raw, so the recursive walk in `module_surface_promote`
does reach them. The surface-matching loop that runs immediately before the
validator compares those fields and works fine.

## Fix

`module_surface_registry.spl`: `module_surfaces_promote` now calls
`module_surface_promote_freeze_names(surface)`, which promotes the four freeze
scope texts explicitly and then fails closed on the post-condition — a second
`rt_transient_heap_promote` reports true only for a value that is STILL owned by
the dying scope, so deleting the four promotions makes the build stop with
"Module surface registry graph promotion failed after phase 2" instead of
SIGSEGV-ing an hour later.

`value_struct_layout.spl` (the surfaced path, hardened but NOT weakened — the
validator still runs, still walks every root, and still reports cycles):

- a module key that does not concatenate into a usable text is reported as
  `internal error: value struct layout module key at index N ...` instead of
  being inserted;
- a node key absent from the struct index is reported instead of having its
  fields dereferenced.

## Reproducer

`test/fixture/transient_scope/text_field_promotion.spl` (run by
`scripts/check/check-transient-scope-text-field-promotion.shs`) — no compiler imports.
Carrier class born and promoted in transient scope A; scope A ends; a fresh text
is assigned into a field in scope B; `rt_transient_heap_promote(carrier)` is
called exactly as `module_surfaces_promote` calls it; scope B ends; the freed
storage is churned. Case A (no explicit field promotion) must report CORRUPT,
case B (the fix) must report OK; any other combination is a failure.
Native only — the transient scope externs are inert under an interpreter.

## OPEN, and deliberately not claimed as explained: a live scope id during phase 3

`roots`, `pending` and the `structs` dictionary — all allocated inside
`validate_value_struct_layouts`, roughly 69 minutes after phase 2 finished —
carry `transient_scope_id = 32` in the core (`0x0000002000000002` /
`0x0000002000000003` at their headers; the layout is confirmed against the
`RtCoreArray` / `RtCoreDict` definitions in the bootstrap-wt tree that built this
binary, and `len`/`cap` read back as 918/1024 and 395, which is exactly the
observed data).

`rt_core_transient_scope_for_new_object()` returns nonzero only while a scope is
`active && !paused`, so **some transient array scope was open and unpaused
during phase 3**. Scope ids are monotonic, so id 32 is an early scope, not one
opened just before validation. This is NOT explained here, and it is not the
crash: the freed `logical_name` strings are established by reading the key string
objects directly out of the core, and they were freed by an earlier scope's end,
not by scope 32 (which never ended). But it means anything phase 3 allocates is
owned by a scope that may still be reclaimed, which is a second latent hazard in
the same machinery. Candidates to check with a phase-instrumented binary:
`lower_streaming_surface_source` (`driver_hir_pipeline_lowering.spl:65,75` —
`begin` and `pause` on the success path) and the phase-2 registry retention
scope (`driver_source_pipeline_parsing.spl:538`), whose `end` return value is
ignored on several paths.
