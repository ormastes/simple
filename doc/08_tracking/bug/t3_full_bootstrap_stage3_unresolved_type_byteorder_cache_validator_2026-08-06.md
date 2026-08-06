# T3 full-bootstrap redeploy blocked: Stage 3 self-host fails, `unresolved type: ByteOrder` in `cache_validator.spl`

Status: OPEN — blocks task "Bootstrap redeploy to get a genuine pure-Simple
binary" (session tracker #18).
Date: 2026-08-06
Area: compiler / self-hosted HIR type resolution (`src/compiler`), bootstrap
pipeline (`scripts/bootstrap/bootstrap-from-scratch.sh`)

> **UPDATE 2026-08-06 (cycle 6) — read the `Effect` facade-collision section at
> the bottom of this file first.** The `ByteOrder` error above was fixed and was
> then replaced by an `Effect` facade collision in
> `src/compiler/50.mir/__init__.spl`. Two earlier attempts (cycles 2 and 3) at
> that collision were landed as commit `9bb8727cbc3` on a WRONG diagnosis and
> did **not** fix it — a Stage 3 replay pinned at that exact commit reproduces
> the identical error. Do not re-try the "a re-exported function taking
> `fn_: HirFunction` materializes `Effect`" theory a fourth time; it is
> disproved below.

## Summary

A full `--full-bootstrap --deploy` run was executed to redeploy a genuine
self-hosted `bin/simple`. The Rust seed/runtime cargo rebuild succeeded
(picking up today's HEAD commits, including `i64.to_char`, `rt_array_data_ptr_u8`,
the `rt_io_file_*` interpreter registrations, and the SIMD FFI alignment fix).
Stage 2 (seed compiling `bootstrap_main.spl`) passed. **Stage 3 (stage2
compiler recompiling itself — the actual self-host check) failed**, and the
wrapper correctly refused to fall back to the seed for the full CLI build:

```
Stage 3: stage2 → bootstrap_main.spl (self-host)
  warning: stage3 self-host failed (exit 1); Stage 4 unavailable
Stage 3 unavailable — no provenance-verified compiler for Stage 4
error: full CLI build requires a verified pure-Simple stage2/stage3 compiler; refusing seed fallback
```

`bin/simple` / `bin/release/x86_64-unknown-linux-gnu/simple` remain the Rust
bootstrap seed. No binary was deployed. `stubs.rs` / `RT_KEEP` was not touched
(out of scope, per task instructions).

## Exact command run

```
sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy \
  --output=build/bootstrap-t3-redeploy-20260806 --progress
```

Full wrapper log:
`build/bootstrap-t3-redeploy-20260806/` (gitignored build output; not
committed). Stage3 native-build log:
`build/bootstrap-t3-redeploy-20260806/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`.

## The actual error

```
[ERROR] phase 3 FAILED
error: in-process native-build: HIR lowering error in src/compiler/driver/cache/cache_validator.spl: unresolved type: ByteOrder
```
(repeated 8×, identical, single distinct symbol/file pair.)

This is a **cold build**: `--full-bootstrap` rebuilt the Rust seed, which
changes `compiler_fingerprint` and invalidates every previously cached native
object (documented behavior, `.claude/rules/bootstrap.md`), so this is not a
stale-cache artifact.

It is also **not** masked by the "bootstrap-flat" weak pipeline described in
`doc/08_tracking/bug/stage3_clean_baseline_is_bootstrap_flat_artifact_2026-08-01.md`
(stage3 normally runs with `SIMPLE_BOOTSTRAP=1` and `SIMPLE_BOOTSTRAP_STAGE4`
unset, which skips MIR lowering/borrow-check for all but the bootstrap entry
module) — this error surfaced as a hard failure even inside that weaker
pipeline, so it is a genuine blocker, not a false-clean measurement issue.

## Evidence gathered (bounded diagnostic pass — not fixed here)

- `src/compiler/driver/cache/cache_validator.spl` contains **no textual
  reference to `ByteOrder` anywhere in the file** (`grep -n ByteOrder
  cache_validator.spl` → 0 hits).
- `ByteOrder` is declared as `enum ByteOrder` in exactly three modules, one per
  lib tier: `src/lib/common/binary_io.spl:26`,
  `src/lib/nogc_async_mut/binary_io.spl:26`,
  `src/lib/gc_async_mut/binary_io.spl:26`. None of these is imported by
  `cache_validator.spl`.
- `cache_validator.spl`'s direct imports are `compiler.driver.cache.cache_types`,
  `compiler.driver.cache.compile_options_hash`, and
  `std.nogc_sync_mut.io.file_ops.{file_modified_time, file_read_bytes}` — none
  of `cache_types.spl`, `compile_options_hash.spl`, or `file_ops.spl` reference
  `ByteOrder` or `binary_io` either (checked directly, one hop).
- No existing bug doc under `doc/08_tracking/bug/` mentions `ByteOrder` or
  `cache_validator` for this failure mode.

This has the same **shape** as the large, previously-catalogued
"self-hosted resolver requires an explicit import path; the Rust seed resolves
flat over the whole loaded closure and masks it" defect class documented in
`doc/08_tracking/bug/selfhost_names_with_no_import_path_masked_by_seed_flat_resolution_2026-08-01.md`
— but that document explicitly scoped itself to the **545 `unresolved name`**
census and left the companion **3345 `unresolved type`** census (same log,
2026-08-01) unclassified and unfixed (see its line noting the totals). This
`ByteOrder` failure is very likely one instance of that unaddressed, much
larger `unresolved type` bucket, not a new defect family — but this was not
proven (no static reachability/attribution proof was done for the *type*
resolver the way the linked doc did for the *name* resolver), and the
file-attribution itself is suspicious (the reported file has zero textual
occurrence of the symbol), so a resolver-side mis-attribution bug is also a
live possibility. Both need a real diagnostic pass, out of scope for this
bounded check.

## Why this blocks task #18

The bootstrap wrapper's Stage 3 gate is intentionally strict: it refuses to
promote/deploy a full CLI build without a provenance-verified pure-Simple
stage2/stage3 compiler, and refuses to fall back to the seed. That gate is
correct behavior, not a bug — it is exactly what prevents silently deploying
a broken or non-self-hosted binary as `bin/simple`. The defect is upstream, in
`src/compiler`'s HIR type resolution reaching `unresolved type: ByteOrder`
(or mis-attributing an error to `cache_validator.spl`) during self-host.

## Suggested next step (not done here)

Apply the same method as
`selfhost_names_with_no_import_path_masked_by_seed_flat_resolution_2026-08-01.md`
to the **type** resolver: enumerate the full `unresolved type` census from a
stage3 log (ideally with `SIMPLE_BOOTSTRAP_STAGE4=1` for the stronger pipeline,
per that doc's own caution about the flat-pipeline masking), classify each
by (declaring-module count, reachability from the using file's import graph),
and confirm whether `cache_validator.spl` is really the site needing the
import, or whether the type-checker error location is wrong.

## Follow-on blocker: `Effect` facade collision in `compiler.mir.__init__`

After the `ByteOrder` import was added, Stage 3 fails one step later with:

```
[ERROR] phase 3 FAILED
error: in-process native-build: HIR lowering error in src/compiler/mir/__init__.spl:
  enum payload dependency `Effect` conflicts:
  `compiler.hir.hir_types::Effect::struct` vs `compiler.mir.mir_effects::Effect::enum`
```
(3x identical.) Note the file in the message is the *module* path; the real file
on disk is `src/compiler/50.mir/__init__.spl` (numbered-layer dirs are reached
through a symlink, so `git` on the un-numbered path fails with "beyond a
symbolic link").

### Correcting the record: cycles 2 and 3 were the WRONG fix

Commit `9bb8727cbc3` removed two blocks of re-exports from
`src/compiler/50.mir/__init__.spl` on the theory that a re-exported FUNCTION
taking `fn_: HirFunction` (whose `effects: [Effect]` field is
`hir_types::Effect`) materialized the struct into the facade's lowering scope:

- cycle 2: `synthetic_driver_registration.{SyntheticDriverRegistrationStatus,
  SyntheticDriverRegistrationPlan, plan_synthetic_driver_registration}` and
  `synthetic_driver_codegen.{apply_synthetic_driver_codegen}`
- cycle 3: `mir_lowering.{MirLowering, MirError}`

**That theory is false.** A callable's parameter and return types are never
materialized during import registration:
`HirLowering.declared_surface_callable_type` returns `nil` outright while
`self.registering_import_symbols` is set
(`src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:430-431`), and the
callable branch (`:874-877`) does no dependency walk at all. Only **composite
fields** and **materialized enum payloads** are walked. Both removals were
therefore no-ops for this error (they are harmless — those re-exports really do
have zero callers — but they fix nothing).

Proof, not reasoning: a Stage 3 replay of the exact recorded stage-3 command on
the tree containing both removals reproduces the identical error, exit 1.

### The actual traced dependency path

Every step below is in
`src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl`:

1. Top-level named imports register with `materialize_enum = true` (`:1572`).
   The facade's `export use compiler.mir.mir_data.{MirModule, MirFunction, ...}`
   is one of them, and it appears **before** the `mir_effects` block — which is
   why the struct is the `existing` side of the message and the enum the
   `wanted` side.
2. `MirFunction`'s terminal declaration is
   `src/compiler/50.mir/mir_instruction_graph.spl:159`, carrying the field
   `type_bindings: Dict<text, HirType>` (`:173`). The composite branch walks
   each field's named dependencies (`:753-761`), so `HirType` is registered next
   with `materialize_enum` still true.
3. `struct HirType` (`src/compiler/20.hir/hir_types.spl:730`) has field
   `kind: HirTypeKind`, so the walk registers `HirTypeKind` — an enum — and the
   enum branch with `materialize_enum = true` calls
   `register_materialized_enum_payload_dependencies` (`:795-799`).
4. `enum HirTypeKind` has the variant
   `Function(params: [HirType], ret: HirType, effects: [Effect])`
   (`hir_types.spl:768`). Walking that payload claims the local name `Effect`
   for `compiler.hir.hir_types::Effect::struct` (`hir_types.spl:912`).
5. The later `export use compiler.mir.mir_effects.{... Effect ...}` claims the
   same local name for `compiler.mir.mir_effects::Effect::enum`, and
   `claim_materialized_payload_binding` raises the error at `:1175`.

### The fix (cycle 6)

`HirType` is load-bearing on `MirFunction`, and `MirFunction` is the facade's
whole reason to exist, so the hir-side binding cannot be removed. The mir-side
one can, because it is dead through this facade: the only two
`use compiler.mir.{...}` sites in the repo are
`src/compiler/70.backend/codegen.spl:15` and
`test/01_unit/compiler/mir_opt/target_family_package_surface_spec.spl:9`, and
neither names `Effect` or `EffectSet`; every real user imports them from
`compiler.mir.mir_effects` directly.

So `Effect` and `EffectSet` were dropped from the facade's `mir_effects`
re-export list (the rest of that block — `AsyncEffect`, `is_async`,
`pipeline_safe`, `NogcInstr`, `nogc`, `BuiltinFunc`, `builtin_effect`,
`builtin_from_name` — is retained; none of those enums has an `Effect` payload,
and the functions are callables, which are never walked). `EffectSet` had to go
as well as `Effect`: its field `effects: [Effect]`
(`src/compiler/50.mir/mir_effects.spl:160`) re-enters the same materializing
walk through the array-element branch (`:757-761`) and re-raises the identical
error on its own.

This is the same remedy as the `BackendKind` / `CompiledSymbolKind` facade
collision documented at the head of `src/compiler/70.backend/backend_types.spl`
— collapse the colliding name to one terminal binding in the lowering scope.

### RED → GREEN method (reusable)

A full `--full-bootstrap` is not needed to exercise this. Every bootstrap output
dir records the exact stage-3 invocation at
`<out>/stage3/<triple>/stage3-command.transcript`, and keeps the `stage2-admitted`
compiler and `stage2-runtime-authority` next to it — replaying that command
against the working tree reproduces Stage 3 alone (~50 min to the HIR error,
peak RSS ~55 GB). Replay driver used here:
`sh <scratch>/replay_stage3.sh {red|green}`, output dir
`build/bootstrap-t3-effect-fix-20260806/` (gitignored).

Watch out for two environment traps while doing this:

- `earlyoom` is live with `--prefer ^(simple|...)`, so it *preferentially* kills
  the stage-3 compiler, which is named `simple`. A SIGTERM / exit 143 /
  "Terminated" is that, not a compile error — always read the log.
- `pkill -f "<pattern>"` where the pattern also matches the agent's own shell
  command line kills the shell issuing it (observed here twice, exit 144).

## Related

- `.claude/rules/bootstrap.md` — T0-T3 tiering and bootstrap command reference
- `doc/08_tracking/bug/deployed_bin_simple_still_seed_2026-08-05.md` — prior
  status; updated with this attempt's outcome
- `doc/08_tracking/bug/selfhost_names_with_no_import_path_masked_by_seed_flat_resolution_2026-08-01.md`
  — same defect *class* (self-hosted resolver stricter than seed flat
  resolution), for names not types
- `doc/08_tracking/bug/stage3_clean_baseline_is_bootstrap_flat_artifact_2026-08-01.md`
  — why a "0 unresolved" stage3 baseline is not proof of a clean tree, and why
  this failure (surfacing even in the flat pipeline) is not that artifact
- `src/compiler_rust/linker/native_binary/stubs.rs` — unrelated, explicitly
  out of scope for this task, not touched
