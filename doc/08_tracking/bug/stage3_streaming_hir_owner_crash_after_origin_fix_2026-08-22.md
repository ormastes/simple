# Stage 3 streaming HIR owner crashes after export-origin convergence

Status: FIX-IMPLEMENTED-VERIFICATION-PENDING (2026-11-02)  
Priority: P0 bootstrap blocker  
Platform: aarch64-apple-darwin  
Observed: 2026-08-22

## Failure

The strict pure-Simple Stage 3 build exits with SIGSEGV immediately after the
streaming surface phase succeeds and HIR typechecking starts:

```text
[EXPORT-ORIGINS] fixpoint pass 2 complete changed=false
[EXPORT-ORIGINS] exit passes_run=2 changed=false
[BOOTSTRAP-PHASE] phase2:parse:done n_modules=0
[BOOTSTRAP-PHASE] phase3:hir_typecheck:start
Segmentation fault: 11
```

`n_modules=0` is intentional for the streaming lane: phase 2 stores the frozen
surface owner in `streaming_module_surfaces_owner` and clears `ctx.modules`.
The crash therefore lies at or immediately inside
`lower_and_check_streaming_surfaces_impl`, before its first HIR progress
receipt.

## Reproduction

Run the admitted low-memory bootstrap on macOS ARM64 with one worker and no
fallback:

```sh
SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_HIR_EXPORT_ORIGIN_TRACE=1 \
sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --bootstrap-receipt=build/bootstrap/admission/stage4-scalar-fix.receipt \
  --backend=cranelift --mode=dynload --strategy=normal \
  --jobs=1 --progress --no-mcp
```

The preceding null dereference in
`module_surface_explicit_import_origin` is independently fixed by keeping its
loop-carried route selection scalar. This report tracks the next ownership
failure only.

## Investigation boundary

Inspect the native representation and receiver-field handoff for:

- `CompilerDriver.streaming_module_surfaces_owner`
- `CompilerDriver.streaming_surface_owner_ready`
- the call from `lower_and_check_impl` to
  `lower_and_check_streaming_surfaces_impl`
- `Option<ModuleSurfacesByName>.unwrap()` at the streaming HIR entry

Do not restore `ctx.modules`, disable streaming, permit seed fallback, or hide
the crash with a nil/default surface. The repair must preserve the retained
surface owner and fail closed on absence.

## Acceptance

1. A focused native reproducer reaches the first streaming HIR progress
   receipt with the retained surface count intact.
2. Strict Stage 3 completes with no seed fallback.
3. Stage 3 provenance/self-verification passes.
4. A regression test exercises the owner handoff under native execution.

Revalidated 2026-11-02: still plausible because Status OPEN; no fixing commit referenced; cannot be reproduced here (aarch64-apple-darwin).

## Analysis (2026-11-02, p0f-3)

Not reproducible on the Windows x86_64 host; analysed by source reading.

- **Code path:** `lower_and_check_streaming_surfaces_impl`
  (`src/compiler/80.driver/driver_hir_pipeline_lowering.spl`, ~line 936) reads
  `self.streaming_module_surfaces_owner` (class field,
  `src/compiler/80.driver/driver_compiler_type.spl:30`, initialised to
  `ModuleSurfacesByName.empty()` with `streaming_surface_owner_ready: false`).
- **Already mitigated (fail closed):** `57271d9ba49` "feat(runtime):
  rt_heap_ref_wellformed formation probe + fail-closed HIR-entry guards" adds,
  before the first field load: the readiness check,
  `rt_heap_ref_wellformed(surfaces)` (rejects a heap payload word of 0 or in the
  zero page; its comment cites this 2026-08-22 incident, a Some-tagged Option
  with payload word 0) and the empty-surface abort `E-DRV-PHASE3-EMPTY-SURFACES`.
  `af74374c355` fixed a lost readiness flag. Both are ancestors of
  `release/1.0.0`. The SIGSEGV can no longer be silent at this site; a
  malformed owner yields a named diagnostic. Why the payload is 0 on aarch64 is
  not independently fixed.
- **Platform-specific?** Probably yes: a malformed Some/Option payload matches
  the aarch64 nil/Option-of-aggregate codegen defect fixed by `2c89727c11c`
  (see `zerokind_is_a_corrupt_aggregate_2026-09-03.md` section 3a). On Windows
  x86_64 the guard is active and the hand-off round-trips correctly.
- **Regression guard added:**
  `test/01_unit/compiler/bootstrap/streaming_surface_owner_handoff_invariant_spec.spl`
  (4 examples, 0 failures on Windows x86_64): initial empty/not-ready state,
  owner content survives a class-field store, reset after reclaim, Option unwrap
  payload intact.
- **Needed to repro/close:** an aarch64-apple-darwin Stage 3 run on a seed built
  after `2c89727c11c`; if it still dies, the symbolized fault (IPS/lldb) at the
  first streaming HIR load, or the `E-DRIVER-HIR-OWNER-MALFORMED` text,
  identifies the remaining producer. Suggested status:
  `fixed_pending_verification`.

TODO(p0f-3): re-run strict Stage 3 on macOS ARM64 with the current seed and
record whether the guard fires or the crash is gone.

## Validity and status decision (2026-11-02, p0-hir-owner)

**Still valid, not obsolete.** Mono removal (erased generics), the nil/Any
unsafe-only rules, target-neutral HIR and the one-process-per-file pipeline do
not remove this path: `lower_and_check_streaming_surfaces_impl`,
`CompilerDriver.streaming_module_surfaces_owner` and
`streaming_surface_owner_ready` are all live on `release/1.0.0`
(`driver_hir_pipeline_lowering.spl`, `driver_compiler_type.spl`,
`driver_orchestration.spl`, `cache/driver_hir_source_body_*_v1.spl`).

**Root cause (best evidence):** a Some-tagged `Option<ModuleSurfacesByName>`
whose heap payload word was 0 on aarch64 — the Option-of-aggregate codegen
defect fixed by `2c89727c11c`. Verified ancestors of `release/1.0.0`:
`2c89727c11c` (producer fix), `57271d9ba49` (fail-closed
`E-DRIVER-HIR-OWNER-MALFORMED` / `E-DRV-PHASE3-EMPTY-SURFACES` guards at
`driver_hir_pipeline_lowering.spl:950-960`), `af74374c355` (lost readiness
flag). No further source change is warranted without a fresh aarch64 fault.

**Host evidence (Windows x86_64):** the regression spec
`test/01_unit/compiler/bootstrap/streaming_surface_owner_handoff_invariant_spec.spl`
could not be re-run on the currently deployed `C:/dev/simple/bin/simple.exe`
(40,717,312 B, 2026-11-02 14:40): the runner aborts with
`semantic: unknown extern function: rt_tuple_len` (binary/source skew, exit 1,
13 s, peak RSS 189 MB) before reaching the spec. Earlier #5855 run: 4 examples,
0 failures.

**Exact verification repro (stage3-only):** on aarch64-apple-darwin with a seed
built at or after `2c89727c11c`:

```sh
SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_HIR_EXPORT_ORIGIN_TRACE=1 \
sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --backend=cranelift --mode=dynload --strategy=normal \
  --jobs=1 --progress --no-mcp
```

Pass = log continues past `phase3:hir_typecheck:start` to the first streaming
HIR progress receipt with no SIGSEGV and neither guard code. If a guard fires,
its text names the remaining producer; reopen with that output.
