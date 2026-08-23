# Stage 3 streaming HIR owner crashes after export-origin convergence

Status: OPEN  
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

## Triage 2026-08-23 — why compile time cannot see this failure

Audited current source after the origin-fix rebase. The crash escapes static
checking for structural reasons, not missing coverage:

1. **The corrupted value is well-typed.** `streaming_module_surfaces_owner`
   is `ModuleSurfacesByName?` (driver_compiler_type.spl:8); `nil` and
   `Some(...)` are both legal at every program point. The phase-2 store
   (driver_source_pipeline_parsing.spl:482-483) and the phase-3 read
   (driver_hir_pipeline_lowering.spl:122-131) live in different `me` methods —
   interprocedural mutable state. The type system has no typestate/definite-
   assignment tracking across method boundaries, so there is nothing to reject.
2. **The defect is introduced below the type system.** Per the retained
   2026-08-22 `.ips` evidence (stage3_selfhost_exit_139 doc): the `Ok`
   discriminant survives while the class payload word is 0 across two
   consecutive `Result<ModuleSurfacesByName, text>` payload boundaries
   (`module_surfaces_freeze` → `module_surfaces_by_name_from_parts` →
   `builder.finish()`). The frontend typechecks source semantics; a native
   aggregate-transport miscompile is by construction invisible to it.
3. **The runtime trap checks the tag, not the payload.**
   `rt_unwrap_or_trap` (src/runtime/simple_core/core_values.spl:78) gates only
   on the enum discriminant (Ok/Some variant hashes) and returns
   `rt_enum_payload(value)` unconditionally — it never validates payload != 0.
   Same for the driver's `== nil` guard: a zeroed payload is not the nil/None
   representation, so the guard reads "present", unwrap "succeeds", and the
   first field load (`ldr [other]`, other==0) is the SIGSEGV.
4. **`.unwrap()` is a runtime operation by design** — no flow-sensitive
   non-null proof exists at compile time; it lowers to `rt_unwrap_or_trap`.

Note: the "prepared repair" recorded 2026-08-22 (change the inner freeze
verdict to `Result<(), text>` so the class is not transported through two
Result payload boundaries) is **not** present in this worktree —
`module_surfaces_freeze` still returns `Result<ModuleSurfacesByName, text>`
(module_surface_registry_index.spl:291). The lossy two-boundary transport is
still live.

## Triage 2026-08-23 (2) — focused reproducer and fault localization

**Focused reproducer found (15 s, no bootstrap needed).** Every retained
self-hosted stage-2 binary on this host segfaults on a *three-line hello
world* (`fn main() -> i64: print("hello") 0`), exit 139, at the same phase
boundary as the full Stage-3 build:

- `bin/local/phase2-aarch64-apple-darwin-codex/simple` (2026-08-22, candidate
  3a59c8a5): `[build] parse 1/1 step 2/6 complete` → `hir 0/1 pending` →
  SIGSEGV.
- `build/bootstrap/stage3/aarch64-apple-darwin/stage2-admitted/simple`
  (2026-08-21): SIGSEGV even earlier, during parse.

**Fault localized by lldb.** Stop at `EXC_BAD_ACCESS (code=1, address=0x0)`
in `hir_cache_closure_digest+36`:

```
hir_cache_closure_digest:
  +28: and  x11, x0, #0xfffffffffffffff8   ; untag arg0 (surfaces)
  +36: ldr  x11, [x11]                     ; load surfaces.surfaces — FAULT
```

`x0 == 0`: the caller `lower_and_check_streaming_surfaces_impl` passed a
literal 0 as `surfaces`. That argument is
`self.streaming_module_surfaces_owner.unwrap()`
(driver_hir_pipeline_lowering.spl:131). The phase-2 guards
(ready-scalar true, `owner == nil` false) all passed, so the Option read back
as **Some-tagged with payload word 0** — the exact payload-loss signature
recorded in the 2026-08-22 `.ips` set. With `SIMPLE_HIR_CACHE=0` the same
binary gets one step further (into lowering of the first module) and dies
there instead — same zeroed owner, later consumer.

**This is NOT the 2026-08-21 NULL-GOT incident.** That class (stage binary
SEGV on hello world via an undefined `rt_unwrap_or_trap` left as a null GOT
slot) is already fail-closed in the seed linker
(pipeline/native_project/stubs.rs:1004-1057). Here the *function* is fine;
the *argument* is 0.

**Corollary: source-era caveats.** The crashing binaries are from 2026-08-21
/ 2026-08-22 source; whether current `main` still mis-lowers the
Option-class field handoff can only be decided by a fresh stage 2 (the
2026-08-19 Rust seed cannot compile current source — `unsafe` unsupported,
E1002). A `--full-bootstrap --stop-after-stage2` rebuild is the admission
gate for the root fix; do not attribute either outcome to this analysis
without that receipt.

**No working compiler on the host for a red/green loop** (2026-08-23):
seed: `unsafe` E1002 on current `src/lib`; deployed
`bin/release/aarch64-apple-darwin-macho/simple`: SMF compile "reported
success without creating" output; both stage-2 binaries: SIGSEGV as above.
All validation of source repairs must go through the staged bootstrap.
