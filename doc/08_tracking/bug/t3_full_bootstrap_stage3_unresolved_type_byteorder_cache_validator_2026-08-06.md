# T3 full-bootstrap redeploy blocked: Stage 3 self-host fails, `unresolved type: ByteOrder` in `cache_validator.spl`

Status: RESOLVED (this symptom) — the `unresolved type: ByteOrder` /
`try_register_bootstrap_global_symbol` lazy-import-registration defect
described below is fixed at `origin/main` (BGS1 fix,
`module_lowering.spl:952-955`) and is now covered by a regression spec:
`test/01_unit/compiler/hir/hir_lazy_import_registration_flag_regression_spec.spl`
(RED confirmed with the fix reverted, GREEN with it restored). Task #18
overall remains blocked by a DIFFERENT, later-discovered issue — see the
"live head is now a vacuous binary" update at the bottom of this file, which
is out of scope for this ByteOrder-specific fix and owned by a separate lane.
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

## UPDATE 2026-08-06 (RXM1 lane): Stage 3 now REACHES this error in 127s instead of never — and it surfaces in `watcher_client.spl`, not `cache_validator.spl`

Until commit `548f2d3b1f6`, Stage 3 could not reach this blocker at all. It was
**non-terminating**: `find_reexport_source`
(`src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:1053`) had no
memo and re-walked a cyclic import graph to its `depth > 8` cap, so the run
climbed to `VmRSS` 39.4 GB over 26 minutes, frozen at `tasks_done=2/6`, with no
signal and no diagnostic, until something external killed it. Full analysis:
`stage3_selfhost_nonterminating_reexport_chase_2026-08-06.md`.

With that fixed, Stage 3 reaches the HIR phase and **fails fast (127s, exit 1)**
here. Two things the next lane should note:

1. **The file is `src/compiler/driver/watcher/watcher_client.spl`**, not
   `cache_validator.spl` as recorded above. Same error text
   (`unresolved type: ByteOrder`). This is either a sibling instance the earlier
   fix did not cover, or evidence that the recorded fix addressed only the
   `cache_validator.spl` path. **Confirm which before assuming this doc's
   earlier "was fixed" line still holds.** (Note the real tracked path is
   numbered — `src/compiler/80.driver/` — since `src/compiler/driver` is a
   symlink and git pathspecs on it fail; error messages report the MODULE path.)

2. **This error is NOT caused by the RXM1 memo.** A wrongly-memoized miss would
   produce exactly this symptom, so it was tested rather than argued: the
   level-gated trace `SIMPLE_HIR_REEXPORT_TRACE_NAME=ByteOrder` recorded **zero**
   MEMO-SUPPRESSED events for `ByteOrder` across a full run. Re-run that trace
   before suspecting the memo.

This is now the first blocker Stage 3 actually reports, so it is the live head
of task #18.

---

## RESOLVED (2026-08-06, BGS1) — the defect was in the resolver, not in any consumer file

`9bb8727cbc3` did **not** regress. Its `use std.binary_io.{ByteOrder}` in
`cache_validator.spl` is intact at `origin/main`, and that file no longer
fails. What happened is the thing this document's own "Suggested next step"
warned about: it fixed **one member of a family** and the next member came
straight up behind it —

```
error: in-process native-build: HIR lowering error in
  src/compiler/driver/watcher/watcher_client.spl: unresolved type: ByteOrder
```

16x (8 per use site x 2 sites), exit 1, ~131s into Stage 3.

### Root cause

`src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:924`, in
`try_register_bootstrap_global_symbol`.

That function performs a genuine import registration, but **lazily** — it is
reached from BODY lowering (`hir_lowering/types.spl:673`, inside
`lower_named_kind`, immediately before the `unresolved type` gate at
`types.spl:784`; and `hir_lowering/expressions.spl:394`) rather than from
Pass 0.

Pass 0 (`module_lowering.spl:1858-1861`) sets `registering_import_symbols` for
exactly the span of `resolve_import_symbols`. That flag is what makes
`declared_surface_callable_type` return `nil` outright
(`module_lowering.spl:430-431`) — which is precisely why a top-level import
**never** lowers an imported type's METHOD SIGNATURES in the consumer's scope.

The lazy path left the flag `false`. So `register_imported_type_methods`
(`module_lowering.spl:1336`) **did** lower those signatures, and every
parameter/return type that the OWNER module imports but the CONSUMER does not
have in scope died as `unresolved type: X`.

### Why a function-local `use` is the trigger

A `use` inside a function body is **discarded outright** by the parser
(`src/compiler/10.frontend/core/parser_stmts.spl:371` -> `parse_use_stmt_inline`
returns a bare `pass`). The name is therefore unbound when the body is lowered,
and falls through to `try_register_bootstrap_global_symbol`.

The control case is what makes this conclusive, and it was measured, not
assumed:

| file | how `ShbReader` is imported | `ByteOrder` in scope | result |
|---|---|---|---|
| `driver/shb/shb_cache.spl` | **top-level** `use` | no | **passes** |
| `driver/cache/cache_validator.spl` | function-local `use` | no (before 9bb8727cbc3) | failed 8x |
| `driver/watcher/watcher_client.spl` | function-local `use` x2 | no | failed 16x |

`shb_cache.spl` imports the *same* `ShbReader`, *also* without `ByteOrder` in
scope, and calls the same `open`/`is_valid` methods that `cache_validator.spl`
calls — and it does not fail. The error depends on **how a name was bound**,
not on what the code does with it. That asymmetry is the entire defect.

(Note this also disposes of two plausible-looking theories: it is not about
which methods the consumer *calls* — `cache_validator.spl` calls only
`open`/`is_valid`/`source_mtime`/`source_hash`, none of which mention
`ByteOrder` — and it is not about `ShbReader`'s fields or method signatures,
which contain no `ByteOrder` at all.)

### The fix

Save, set, and restore `registering_import_symbols` around the registration, so
the lazy path behaves exactly as Pass 0 already does:

```
val saved_registering_import_symbols = self.registering_import_symbols
self.registering_import_symbols = true
self.register_imported_symbol(owner, owner.module_name, name, name, span, true)
self.registering_import_symbols = saved_registering_import_symbols
```

Saved and **restored**, not cleared: Pass 0 walks composite fields and lowers
their types, which can re-enter `lower_named_kind` and arrive here with the flag
already `true`; clearing it unconditionally would corrupt the in-progress Pass 0.

### Why the resolver layer, and not per-site `use` imports

Because the affected set is **not statically enumerable**. It is "every name
that reaches `try_register_bootstrap_global_symbol` under `SIMPLE_BOOTSTRAP=1`
whose resolved owner's method signatures reference a type absent from the
consumer's scope". A function-local `use` is only *one* way to produce an
unbound name, so the 62 function-local `use` statements in `src/compiler` are
**not** the family — that list is wrong in both directions (it includes sites
that never fail, and misses unbound names produced any other way).

Per-site imports fix one member and leave the rest. That is exactly what
happened with `9bb8727cbc3`: `cache_validator.spl` was fixed, and
`watcher_client.spl` was next in line. One resolver-side guard retires the whole
class at once.

The `use std.binary_io.{ByteOrder}` added to `cache_validator.spl` by
`9bb8727cbc3` is left in place. It is now believed redundant, but that was NOT
verified by a run with it removed, so it is not claimed as subsumed.

### RED -> GREEN -> SABOTAGE

Method: replay Stage 3 alone against a pinned worktree
(`/home/ormastes/dev/simple-s3bisect`, verified byte-identical to `origin/main`
for every file touched), using `build/cyc/build_stage2.sh` +
`build/cyc/run_stage3.sh`. The fix is in the COMPILER, so each cycle must
rebuild stage2 from the seed — stage2 rebuild ~2m50s, stage3 to the HIR wall
~2m. Far cheaper than the ~50min full-bootstrap replay this doc previously
recorded.

| run | tree | STAGE3_EXIT | wall | `unresolved type: ByteOrder` | phase reached |
|---|---|---|---|---|---|
| `GRN2RUN` / `VER2RUN` (RED) | origin/main | 1 | 127-131s | **16** | `phase=hir`, `failed=1` |
| `FIX1RUN` (GREEN) | + BGS1 fix | 139 | 394s | **0** | `phase=monomorphize`, `tasks_done=4/6`, `failed=0` |
| `SAB3RUN` (SABOTAGE) | fix reverted | 1 | 129s | **16** | `phase=hir`, `failed=1` |

HIR lowering — the phase that hard-failed in every prior run — now completes
clean, and Stage 3 advances two further pipeline tasks.

### Status: past this wall, next blocker is different

Stage 3 does **not** complete, and no `stage3-simple` binary is produced. It now
dies later and differently: **SIGSEGV, exit 139, "dumped core"**, at 394s, peak
RSS 10.7 GB, during `phase=monomorphize` / MIR lowering. The last log lines are
`[mir-lower-expr] int:start / int:builder / int:emitted / int:done`.

This is a *signal*, not a diagnostic — exit 139 with no `error:` line. It is
distinct from the three failure modes already catalogued here: not the 60s
timeout (255), not the `--budget` SIGKILL (137), not an `earlyoom` kill (143,
and peak RSS was well under budget anyway).

It is also NOT the stack-overflow fixed by `030ff43e330` and NOT the
non-termination fixed by `548f2d3b1f6` — both of those are upstream of HIR
completion, which now passes.

Most likely the same "pre-existing native-build instability" named as the
blocker in
`doc/08_tracking/bug/mir_lowering_codegen_error_first_call_zero_core_dump_2026-08-06.md`,
whose own `CompileResult.CodegenError` source fix is already present at
`origin/main` (verified: all call sites in `driver_aot_pipeline.spl`,
`driver_pipeline_execution.spl`, `driver_orchestration.spl` carry the fixed
form). That doc could not verify itself against a rebuilt stage3 because Stage 3
never got this far; this run is the first to reach that ground. Attribution is
stated as likely, not proven — no core-dump analysis was performed here.

That MIR-lowering segfault is the new live head of task #18.

## 2026-08-08 UPDATE: the segfault is GONE; the live head is now a vacuous binary

The sentence above is superseded. Re-running Stage 3 on the same pinned
worktree (`22dd136685d`) with the same stage2 (`S3FIX1`) and only the wall
budget raised from 900s to 3600s:

```
STAGE3_EXIT=0   WALL=1202s   PEAK_RSS_KB=10,667,012
last log line: [llvm-tools] read-bytes
error: lines: 0     const-0 placeholder warnings: 3,629
```

**Stage 3 runs to completion and exits 0.** Exit 139 / "dumped core" did not
reproduce. Note 1202s > the 900s budget the earlier FIX1RUN-era runs were given,
so at least part of the previously-recorded instability was the budget, and the
attribution of the 394s SIGSEGV should be treated as unreliable rather than
carried forward. No core-dump analysis is claimed here either way.

**But exit 0 is not success.** The `-o` artifact is a vacuous 22,896-byte
`stage3-simple` — 14 KB `.text`, 42 functions, all-libc dynamic symbols, a
`main` that calls `__simple_main` (which reads uninitialised stack and returns)
and exits 0 printing nothing. The real object is written beside it and never
linked: `stage3-simple.app.cli.bootstrap_main.o`, 1.16 MB, 209 KB `.text`,
5,869 defined symbols including `bootstrap_compile_backend_from_args`.

Reproducible and deterministic — three runs of different durations produced a
byte-identical artifact (md5 `401436362a7c`): S3RUN12 529s, S3RUN_LONG 948s,
S3RUN_3600 1202s/exit 0. The differing wall times rule out the harness budget.

This is precisely the documented `native-build exits 0 producing nothing` trap.
Any gate reading exit status or `error:` lines passes this run. The live head of
task #18 is now **"the compiled object is not linked into the output binary"**,
and the honest completion test is a symbol count on the emitted binary, not the
exit code.

Cross-referenced in
`doc/08_tracking/bug/mir_unresolved_method_const0_fails_open_2026-07-28.md`,
which also records the 3,629-substitution / 538-name census showing that
`0 error: lines` is a fail-open reading in this lane.

## 2026-08-18 RE-PROBE: still resolved under the freshly rebuilt seed

The deployed seed was rebuilt 2026-08-18 06:12 (brace-escape + statx +
env-cache fixes; the env-cache change touched interpreter-adjacent code, so
this re-probe was genuinely informative, not ritual). T0 hosted-seed probes:

1. Regression spec (foreground, `bin/simple test`):
   `test/01_unit/compiler/hir/hir_lazy_import_registration_flag_regression_spec.spl`
   → `SPEC FILE VERDICT: ... outcome=OK declared>=1 executed=1 passed=1 failed=0`
   → `Results: 1 total, 1 passed, 0 failed` (PASS, exit 0).
2. Minimal lazy-import probe (`use std.binary_io.{ByteOrder}` + match on
   `ByteOrder.LittleEndian`, run via `bin/simple run`): prints
   `PROBE_BYTEORDER=little`, exit 0. This probe is now permanently fenced as
   check 3 of `scripts/check/check-bootstrap-preflight.shs` (fatal --selftest,
   PASS/SKIP/FAIL/ERROR verdict per the detector standard).

Conclusion: the `unresolved type: ByteOrder` defect remains RESOLVED; the
stale KNOWN BLOCKER section in `.claude/rules/bootstrap.md` has been annotated
accordingly (2026-08-18).
