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

## Triage 2026-08-23 — macOS arm64 lane analysis (ported), cross-checked on Linux x86_64

**Provenance:** everything under this heading was measured by the **macOS
aarch64 lane** (`origin/codex/stage3-hir-owner-fixes`, commits `6781f4bcdf0`
and `c9ce33e2234`) unless marked *[linux x86_64, this lane]*. Ported here by the
Linux sync lane; each claim below was re-checked against `origin/main` source on
Linux and the verdict is recorded inline.

### Why compile time cannot see this failure (macOS lane)

1. **The corrupted value is well-typed.** `streaming_module_surfaces_owner` is
   `ModuleSurfacesByName?`; `nil` and `Some(...)` are both legal at every
   program point. The phase-2 store and the phase-3 read live in different `me`
   methods — interprocedural mutable state, and there is no typestate /
   definite-assignment tracking across method boundaries to reject.
2. **The defect is introduced below the type system.** The `Ok` discriminant
   survives while the class payload word is 0 across two consecutive
   `Result<ModuleSurfacesByName, text>` payload boundaries
   (`module_surfaces_freeze` -> `module_surfaces_by_name_from_parts` ->
   `builder.finish()`). A native aggregate-transport miscompile is by
   construction invisible to a frontend that typechecks source semantics.
3. **The runtime trap checks the tag, not the payload.** `rt_unwrap_or_trap`
   gates only on the enum discriminant and returns `rt_enum_payload(value)`
   unconditionally — it never validates payload != 0. The driver's `== nil`
   guard has the same hole: a zeroed payload is not the nil/None
   representation, so the guard reads "present", the unwrap "succeeds", and the
   first field load faults.
   *[linux x86_64, this lane] — CONFIRMED verbatim on `origin/main`:
   `src/runtime/simple_core/core_values.spl:79-100`, `rt_unwrap_or_trap`
   branches only on `rt_enum_id` / `rt_enum_discriminant` and returns
   `rt_enum_payload(value)` with no payload validation. Platform-independent —
   this is Simple source, not a Darwin artifact.*
4. **`.unwrap()` is a runtime operation by design** — no flow-sensitive
   non-null proof exists at compile time; it lowers to `rt_unwrap_or_trap`.

**Lossy transport still live.** *[linux x86_64, this lane] — CONFIRMED:
`module_surfaces_freeze` still returns `Result<ModuleSurfacesByName, text>` at
`src/compiler/20.hir/hir_lowering/module_surface_registry_index.spl:291` on
`origin/main`. The prepared repair (inner freeze verdict -> `Result<(), text>`,
so the class is not transported through two Result payload boundaries) is NOT
applied on either tree.*

### Focused reproducer and fault localization (macOS arm64 — platform-specific evidence)

15 s, no bootstrap needed: every retained self-hosted stage-2 binary on the mac
host segfaults on a three-line hello world (`fn main() -> i64: print("hello")
0`), exit 139, at the same phase boundary as the full Stage-3 build —
`[build] parse 1/1 step 2/6 complete` -> `hir 0/1 pending` -> SIGSEGV. lldb
stops at `EXC_BAD_ACCESS (code=1, address=0x0)` in
`hir_cache_closure_digest+36` (`ldr x11, [x11]` after untagging arg0), with
`x0 == 0`: the caller `lower_and_check_streaming_surfaces_impl` passed a literal
0 as `surfaces`, i.e. the Option read back **Some-tagged with payload word 0**.
With `SIMPLE_HIR_CACHE=0` the same binary reaches lowering of the first module
and dies there — same zeroed owner, later consumer. The register/disassembly
evidence is aarch64-specific; the *class* (Some-tag + zero payload) is not.

### Two distinct SEGV classes — both lanes agree, and this is the load-bearing point

| | macOS aarch64 lane | Linux x86_64 lane (this repo) |
|---|---|---|
| class | **zeroed Option payload** | **NULL GOT slot** |
| signature | `x0 == 0` passed into a live function; `rip` valid | `rip == 0`; the function itself never existed |
| cause | native aggregate transport loses a class handle across two `Result` payload boundaries | codegen emitted a call to undefined `rt_unwrap_or_trap`; link tolerated it, GOT slot stayed zero |
| root-caused at | (open) | `c4b84dc9aaf` |
| fail-closed by | `rt_heap_ref_wellformed` driver guards (`57271d9ba49` here, `4dd2f956a83` there) | seed linker `pipeline/native_project/stubs.rs` |

The macOS lane states explicitly that its crash is **NOT** the NULL-GOT
incident ("the *function* is fine; the *argument* is 0"). The Linux lane
independently root-caused its own stage3 SEGV as NULL-GOT. **These agree: they
are two different defects that present identically as "stage binary SEGVs on
hello world", and a hello-world SEGV must therefore be classified by
`rip == 0` vs `arg == 0` before anything else is concluded.** Fixing one does
not fix the other, and a green NULL-GOT gate is not evidence about this bug.

### Caveats carried over verbatim

- The crashing mac binaries are from 2026-08-21/2026-08-22 source. Whether
  current `main` still mis-lowers the Option-class field handoff can only be
  decided by a fresh stage 2; do not attribute either outcome to this analysis
  without that receipt.
- On the mac host there was **no working compiler for a red/green loop** on
  2026-08-23 (seed: `unsafe` E1002 on current `src/lib`; deployed binary: SMF
  compile "reported success without creating" output; both stage-2 binaries:
  SIGSEGV). All validation of source repairs there goes through the staged
  bootstrap. *[linux x86_64, this lane] — the `unsafe` half is confirmed
  portable: `origin/main` `src/lib/**` contains 2,245 `unsafe(` uses, so any
  seed predating ~2026-08-19 fails with `error[E1002]: function 'unsafe' not
  found` on any host. This is a source-era fact, not a Darwin fact.*
