# MCP native build: `method 'contains' not found on type 'nil'` immediately after monomorphization

**Date:** 2026-09-01 · **Status:** OPEN · **Severity:** blocker (last thing between the MCP build and MIR lowering)

## Provenance
HEAD `ec054763e96` (on top of `9fb0d279739`), seed
`src/compiler_rust/target/release/simple.exe` md5
`286f66b8615dce0e0da788f0550c4008`. `SIMPLE_EXECUTION_MODE=interpret`,
`SIMPLE_NATIVE_BUILD_WORKER=1`, `SIMPLE_RESOLVE_METHODS` unset (default OFF).

```
bin: simple.exe run src/app/cli/native_build_worker.spl src/app/mcp/main.spl
```

## How far the build now gets (rc=1, ~21 min)
```
step 1/6 parse           100/100 OK
step 1/6 surface_build   100/100 OK
step 2/6 hir             100/100 OK        [hir-cache] hits=100 misses=0
         any-escape pass      548 diagnostic(s)   (warnings)
         enum-contract pass     0 diagnostic(s)
         [mono] generic_fns=0 call_sites=0 specializations=0 unresolved=0
         0 compile errors  (SIMPLE_DUMP_COMPILE_ERRORS=1 -> zero [compile-error] lines)
error: semantic: method `contains` not found on type `nil` (receiver value: nil)
```
This is the FIRST time the build has cleared HIR entirely. It dies between the
`[mono]` receipt (`driver_hir_pipeline_passes.spl:129`) and MIR lowering, so the
candidate region is the `mono_diags` loop, `record_pass_receipt`, or
`post_mono_verify_modules` / `post_mono_report_*` that follow it
(`driver_hir_pipeline_passes.spl:129-175`).

## Not yet pinned
`SIMPLE_DEBUG_FIELD_ACCESS=1` and `SIMPLE_INTERP_OOB_DEBUG=1` print NOTHING for
this one — the seed's `[field-access-error]` probe covers field access, not a
method-not-found on a nil receiver. There is no equivalent
`[method-call-error]` dump. Next step is either to add one to the seed, or to
bisect with `eprint` probes across `driver_hir_pipeline_passes.spl:129-175`
(each full run costs ~21 minutes; surface_build alone is ~19 of them).

## Defect family
Same shape as the two already fixed today: a provider returns nil/a status
where the caller expects a collection, and the member access is fatal. See
`doc/08_tracking/bug/mcp_native_build_hir_entry_env_get_nil_len_fatal_2026-09-01.md`
and `doc/08_tracking/bug/self_rooted_chain_val_binding_clobbers_receiver_2026-09-01.md`.

## MIR error count
Still NOT obtainable — MIR lowering (step 3+/6) is never entered. The last
real full-build number remains 133, measured before this lane's fixes.

## Lead REFUTED by experiment (2026-09-01)
Hypothesis: the nil receiver was one of the three `text.contains(...)` calls in
`src/compiler/40.mono/verify/post_mono_verify.spl`
(`check_mangling` lines 586/590, `enter` line 603) reached with a nil HIR
definition name. All three were nil-guarded (`?? ""`) and the full build re-run:
**identical failure, same message, same position** (hir 100/100, any-escape 548,
enum-contract 0, `[mono] generic_fns=0`, then
`error: semantic: method \`contains\` not found on type \`nil\``).
The guards were therefore REVERTED rather than left as speculative dead
robustness. The site is elsewhere in the post-mono -> MIR-entry region, and the
region is wider than the "129-175" first written above: no receipt prints
between the `[mono]` line and the (never reached) step 3/6 announcement, so
nothing bounds it at 175.

Next lead, in cost order:
1. add a `[method-call-error]` dump to the seed's method-not-found path — the
   sibling of the existing `[field-access-error]`, which is what pinned the HIR
   blocker in minutes; it prints nothing for a method-not-found today;
2. failing that, `eprint` bisection across the post-mono region (~21 min/run).

## `SIMPLE_DUMP_COMPILE_ERRORS` gate verified both ways (2026-09-01)
The gate reads the ambiguous `env_get` (6 co-compiled defs, 2 signatures), so it
was tested rather than assumed, using the worker on a 2-line file with a
deliberate unresolved name:
- `SIMPLE_DUMP_COMPILE_ERRORS=1` -> `[compile-error] HIR lowering error ...:
  unresolved name: definitely_not_a_real_symbol` (1 line), then the usual
  `phase 3 FAILED (diagnostics unreadable...)`;
- unset -> **0** `[compile-error]` lines.
So the dump fires when asked and is silent by default.
