# Stage-2 sanity: stage2_module_path_naming probe SIGSEGVs the worker (2026-10-22)

Status: OPEN — blocks the full stage2 sanity battery; p2_add (the compile/run
admission probe) PASSES. Phase 3 + phase-2 validation proceed provisionally
from the hello-world gate per the parallel collection policy (descendants
unadmitted until this closes).

## Symptom

`candidate_frontend_smoke` p2_add, scv_prime and the mir-retention probe pass;
the `stage2_module_path_naming.spl` probe (and then hello-world-positional)
kills the native-build worker with SIGSEGV during the HIR phase:

```
[build] phase=hir ... current=compiler.bootstrap_admission.stage2_module_path_naming
[hir-cache] disabled reason=no-compiler-scope
[WARN] any-escape pass: 0 diagnostic(s)
/usr/bin/timeout: the monitored command dumped core
Segmentation fault
error: stage2 failed the positional pure-Simple Stage-3 route (status 139)
```

Reproduces with the stage2 candidate under the sanity-like env
(`SIMPLE_BOOTSTRAP` unset, `--runtime-bundle core-c-bootstrap
--entry-closure --entry src/compiler/bootstrap_admission/stage2_module_path_naming.spl`).

## Context

The fixture's own header documents a KNOWN unresolved lane defect it
exercises: cross-module plain calls do not link in the per-module one-binary
lane (bare vs qualified symbol spelling; fix NOT landed as of 2026-10-17).
The previous failure mode of this lane was a clean link error; on the current
release_phase3 tree the worker SEGSEGVs instead.

A sibling defect in the same area was fixed today and may share a root cause:
`state = self.live_aliases(state, ...)` in the NLL solver corrupted the array
argument in transit (deterministic garbage header at callee entry);
moving the callee to module scope as a free function
(`nll_live_aliases`, e10fbb8f766 / 4f41ac876d8) fixed that instance. The
method-call argument-passing miscompile family (see cce1cddae19, mir receiver
writeback) likely has more instances reachable through this fixture's shape.

## Next steps

1. Replay the failing probe's worker under gdb (extract argv via strace on
   the coordinator, run `simple run src/app/cli/native_build_worker.spl ...`
   directly) and symbolize — the binary carries function symbols.
2. Audit the HIR-phase call path the fixture exercises for the same
   `self.method(array_arg, ...)` shape and convert to module-scope free
   functions as a targeted workaround.
3. Land the actual codegen fix for the argument-corruption family.

## Update 2026-10-22 (evening): deterministic on pristine state; crash path isolated

- Reproduced with a COMPLETELY fresh sanity state (stage2-home/stage2-tmp
  wiped) on HEAD 7f9a8c802a3: the probe SEGV persists — it is not
  accumulated-state corruption.
- The sanity probe runs the HIR phase with `[hir-cache] disabled
  reason=no-compiler-scope` (frontend_parse_cache_scope()=="" — the SCV
  admitted-epoch probe context). Manual reproductions all ran WITH the cache
  scope and pass; forcing `SIMPLE_HIR_CACHE=0` (reason=off) also passes. The
  crash therefore lives in the no-compiler-scope HIR lowering path, only
  reachable under the sanity's scrubbed SCV-epoch environment.
- The bounded collector sets RLIMIT_CORE=0, so no core is available; under
  gdb the coordinator path does not crash (timing/layout heisenbug).
Next actionable step: instrument the no-scope HIR lowering path
(driver_hir_pipeline_lowering) with an env-gated progress trace, rebuild the
candidate, and rerun the wrapper sanity to see the last successful operation
before the fault.

## Update: trace bracket (SIMPLE_NSCOPE_HIR_TRACE, landed passthrough)

Instrumented `lower_retained_surface_module` (retained-enter/retained-lowered)
and `_driver_module_aliases_with_closure` (aliases-enter), with the env
surviving the sanity scrub via the wrapper's inline `bootstrap_stage_sanity`
passthrough (commit "debug(sanity): passthrough ...").

Result: for the passing p2_add probe all milestones fire (retained-enter →
retained-lowered → aliases-enter, across both sanity passes and shard
re-entries). For stage2_module_path_naming.spl NO milestone fires — not even
aliases-enter — so the SIGSEGV happens at or before entry source processing:
in the entry PARSE or the load/scan/module-name derivation stage, inside the
sanity's scrubbed SCV-epoch environment. The same candidate parses and
compiles this exact file successfully outside the sanity (multiple manual
runs, cold HOME, cache off, delegate env). The file itself is a verbatim
mirror of `src/compiler/00.common/module_path_naming.spl` (235 lines, kept in
sync by header rule; the real functions live there).

Next step: instrument the parse-shard / entry-scan path
(driver_source_pipeline_loading entry scan, parse_full_frontend_selected_v1)
with the same env-gated trace to bracket the exact operation; suspect an
env-dependent parse path (package-index cold route) interacting with this
file's multi-line `or` continuations / docstring content.

## Update: symbolized backtrace (p2_add reproduces manually since merge 05157642057)

gdb on the exact worker argv (strace-captured) deterministically catches:

```
#0 module_surface_semantic_projection +5580   <- nearest-symbol; likely a
                                                  following static helper
#1 module_surface_from_owner (module_surface_declarations.spl:209)
#2 ModuleSurfaceBuilder.add_parsed_canonical (module_surface_registry)
#3 CompilerDriver.parse_all_impl
```

The fault fires during parse-all's surface projection of the freshly parsed
canonical module — between the alias scan (trace fires) and retained lowering
(trace silent). The [proj] entry trace in the projection does NOT fire even
though the crash symbolizes inside the function — consistent with the PC
landing in a STATIC helper laid out after it (the file's `_surface_mix_text`
byte loop over a garbage text field is the prime suspect; the source already
carries three rounds of "ANY-transport hazard sweep: annotated rebind"
defenses, so the corrupting transport shape is one the sweeps miss).

The same defect family explains this lane's earlier manifestations:
NLL live_aliases method-arg corruption (fixed by free-function conversion)
and the original module_path_naming sanity-only SEGV (same bracket).

Also ruled out this cycle: PR #4133's fs.spl Any-expansion variant as the
Linux cause (restored the two-arg text form — landed, matches the pre-merge
proven shape; crash persists, so the regression trigger is the binary-layout
shift, not the file-io path). io_file.rs changes are Windows-only; the
collections.rs merge correctly retains both promote exemptions.

Next: either compile a -g (line-info) candidate for an exact fault line, or
move per-helper env-gated traces into _surface_fold/_surface_mix_text/
_surface_function to name the corrupting field.

## Update: DEFINITIVE root cause — class-with-large-struct-field read returns garbage

Trace chain (all committed): `module_surface_from_owner` entry prints with a
valid owner reference (`owner_nil=false`); `val module_local: ParserModule =
owner.value` then reads `module_local.name.len() == -1` and
`module_local.functions.len() == -1` — the struct FIELD of the class
`ModuleSurfaceParserOwner` (`value: ParserModule`, a 15+ field struct stored
inline) reads back garbage in the self-hosted candidate. The callee
(`module_surface_semantic_projection`) consequently SIGSEGVs in its prologue
before executing any body statement (an unconditional entry eprint never
printed; the crash PC lands in the callee's symbol region — a nearest-symbol
artifact). Local binds at BOTH the call site and the wrapper constructor
(`static fn new(value: ParserModule)`) do NOT rescue it — the corruption is
the class field store/read itself for large inline struct fields.

This is the same by-value/aggregate-transport family as the NLL
`live_aliases` array-argument corruption (fixed by module-scope free-function
conversion) and the poll/future generic-enum-pattern case (fixed by local
bind — shallower shape).

Source-level workaround candidate (not yet attempted): flatten
`ModuleSurfaceParserOwner` to handle-sized fields (`name: text`,
`functions: Dict<...>`, … one slot per ParserModule limb, all 8-byte
handles/texts) and reconstruct the ParserModule at the use site — avoiding
any large inline-struct class field. The proper repair is in the compiler's
class-field layout/copy for large inline structs.

## Update: flatten workaround IMPLEMENTED (release/1.0, 2026-10-22)

`ModuleSurfaceParserOwner` no longer has a `value: ParserModule` class
field. It now stores ONE SLOT PER ParserModule LIMB (30 handle-sized
fields: texts, Dicts, arrays, bools, i64s) with an annotated typed-local
rebind per limb in `new()`, and the new exported
`module_surface_owner_value(owner) -> ParserModule` reconstructs the
ParserModule by named construction at the use site. Call sites migrated
to the reconstruction as the single sanctioned read path:
- `module_surface_from_owner` (all `owner.value.*` reads replaced by the
  reconstructed `module_local`)
- `driver_native_parser_impls_are_enum_templates_v1`,
  `driver_native_parser_is_declaration_only`,
  `driver_native_parser_can_persist_objectless` (typed local `value` bind)

Single-field class reads/writes of handle-sized types are exercised
throughout the self-hosted candidate; the 30-limb reconstruction only
relies on those. The proper repair (compiler class-field layout/copy for
large inline structs) remains open — this workaround should be reverted
once it lands.

Same session also fixed: `src/compiler_rust/Cargo.lock` had 273 orphaned
entries after the LLVM-major-23 gate slimmed llvm-sys (110-221,
stacker/psm, gumdrop, pest, semver 0.11); every `cargo build --locked`
seed lane failed. Regenerated offline against vendored sources.
## Update: HIR-phase campaign (same session, release/1.0)

Fix landed order (PR #4162 = 85b31bb4802 + 43921b1dbd3 + 8a447adbdb4):

1. `driver_register_parser_module_source_aliases_v1` took ParserModule BY
   VALUE → SIGSEGV (garbage Dict handles). Now routed through the flattened
   `ModuleSurfaceParserOwner`; callers typed-bind Dict values and unwraps.
2. gdb disassembly at the next crash PROVED seed-emitted mis-dispatch:
   `ldr x8,[x27,#352]; mov x0,x8; bl EnumContractTable.has` — `.has` on the
   `HirFieldTypesByName` ALIAS-typed class field resolved to the wrong
   struct's method (x0 held the Dict header word 0x2000000003). All 10
   alias-typed dict fields of class HirLowering expanded to literal dict
   types. Literal-typed fields resolve correctly (ParserModule.enums.has).
   Proper repair: seed/frontend method resolution on alias-typed receivers.
3. After those: no crash; sanity passes ALL surface phases; p2_add HIR
   lowering RUNS but `driver_publish_reverse_reference_parse_scope_v1`
   fails at the facts step. SIMPLE_NSCOPE_HIR_TRACE=1 sub-step trace:
   seal OK, scope-end OK, reverse_reference_module_publish_v1 FAILED.
   Env-gated refusal-reason trace landed to name the guard.

## Update: publish gate root cause DEFINITIVE (2026-10-23)

Traced (`SIMPLE_NSCOPE_HIR_TRACE=1`) through the retained p2_add HIR path:
seal OK, scope-end OK, `reverse_reference_module_publish_v1` refuses with
`batch_token=1023114373 gen=1/1 active=true sealed=true valid=true` — every
guard correct EXCEPT the batch's token limb, which reads back garbage after
`transient_promote` of the Option carrier + transient scope end. The promoted
Option keeps referencing the reclaimed transient slot; the token limb is
clobbered first, and with the token check relaxed the publish body then HANGS
on the same stale arrays (facts/aliases limbs). Reverted the relaxation —
clean refusal beats a hang.

Root cause class: the candidate's `transient_promote` of an Option<struct>
carrier does not survive scope end (same by-value/aggregate-transport family
as every other 2026-10-22/23 finding). The reverse-reference batch machinery
cannot be unblocked by source-level guard tweaks; it needs either (a) a
candidate/seed promote repair, or (b) restructuring the batch out of the
promoted-Option pattern (module-scope scalar/array limbs promoted
individually, mirroring the ModuleSurfaceParserOwner flatten).

Gate state: stage2 compile 1487/1487 clean; sanity passes ALL surface phases;
p2_add HIR lowering RUNS to completion; blocked ONLY at the reverse-reference
batch publication above.

## Update: frontier moved past publish (2026-10-23, post scalar-mirror)

With the parallel session's scalar-mirror workaround (ab07dfa3567) in, the
p2_add worker now completes the retained HIR lowering (52.9 s for the tiny
module — pathological slowness remains) and stores it to the hir-cache, then
fails at:

  NOGC-POLICY-001: cached HIR ownership policy disagrees with its declaring
  source

A second state-dependent failure mode is a spinlock hang
(`__aarch64_swp4_rel` atomic-swap loop, gdb SIGINT stop) in the HIR shard
worker when the flock-based shard-recovery queue dir is in a stale state —
fresh queue dirs avoid it. Frontier blockers now: (1) NOGC-POLICY-001 policy
gate (parallel session's active lane), (2) shard-recovery spinlock hang,
(3) 52.9 s pathological HIR time for a 487-byte module.

## Update: publish deadlock FIXED (2026-10-23, PR #4189)

The deterministic phase=hir hang was gdb-caught as a spinlock:
`__aarch64_cas4_acq <- Mutex<i64>::lock <- is_registered_heap_ptr <-
validate_heap_obj <- rt_array_get <- reverse_reference_module_publish_v1`.
The promoted batch Option's scalar limbs were mirrored (ab07dfa3567) but
its ARRAY limbs still referenced reclaimed transient slots; publish's
merge loop read them and spun in the runtime heap registry mutex. Fix:
seal promotes each array limb pre-scope-end (handles still valid) and
mirrors the persistent handles into module globals; publish merges from
the mirrors. Verified: the worker that hung now completes HIR (65 s —
pathological slowness persists) and exits normally.

Remaining frontier for the stage2 smoke (exit 124): the hir-cache STORE
fails at rt_file_write_text (io-write, even to a private cache dir), so
the module is re-lowered on the next pass — doubling an already ~65 s
HIR phase and blowing the smoke's per-probe budget. This is the parallel
lane's documented io-write/encode-pool defect; see
stage2_mir_shard_flat_pool_text_len_minus1_2026-10-22.md.

## Update: the ~65 s HIR phase is NOT lowering (2026-10-23)

SIMPLE_HIR_PHASE_PROFILE=1 on the p2_add worker:
`total=1ms imports=0ms declare=0ms enums=0ms functions=1ms/5` — HIR
lowering of the 487-byte module takes ONE millisecond. The 30–65 s
phase=hir dt is entirely post-lowering, inside the store chain
(hir_cache_store's own scope: encode + hir_module_decode_stable + write)
plus heap-registry mutex contention that varies 30–65 s with system load
(the worker sometimes finishes in <40 s under gdb when the host is
quiet). So the smoke's exit-124 budget pressure is (a) the parallel
lane's parse-pool blob lifetime (store failures force re-work) and (b)
contention-sensitive codec/validation cost — both outside the lowering
path itself.

## Sibling line release/1.0.0 (ported with af10da4f592 / PR #4249)

The release/1.0.0 line tracks this bug under its own update history. The two
entries below back the fold-visitor regeneration and the env-restore unwrap
landed here; the rest of that history stays on release/1.0.0.

### Update 2026-10-24 (x86_64 Linux): `[]` literal SIGSEGV — ROOT CAUSE is the generated fold walker

After #4217 (codec fail-closed) and #4230 (link fix), CI run 39952380127 (release/1.0.0 @
`a5aa33bc618`, linux-cranelift) still failed Stage 2 sanity on this probe, now later:

```
#0 compiler.hir.generated.hir_visitor.walk_hir_type
#1 walk_hir_expr      (ArrayLit arm)
#2 walk_hir_stmt / #3 walk_hir_block
#4 representation_boundary.unsafe_observations.representation_observe_function_v1
#7 driver_hir_pipeline_passes.run_representation_manifest_pass
```

Bisected with the CI's rejected Stage 2 binary down to `fn main(): var out: [text] = []`. Every
empty array literal crashes it (the empty path is where lowering stores `Some(default)` as the
element type).

Root cause, from gdb memory at the fault: the object `walk_hir_type` receives has a heap header
in its first two words (`0x0000001800000007`, `0xf198715900000001`) and the real `HirType`
pointer as payload at +16. In other words, it is the `Some` box. The generated fold walker
`hir_visitor.spl` (from `src/app/compiler_schema/fold_gen.spl` `_fold_lines`) emitted
`acc = walk_hir_type<C>(b_type_, acc, f)` for `ArrayLit(elements, type_: HirType?)`, passing the
Option straight into a `HirType` parameter. Its sibling `hir_visit.spl` (`visitor_gen.spl`)
already unwraps with `match b_type_: case Some(opt1): ...`. The interpreter tolerates the
un-unwrapped form, so only native Stage 2 faults.

Fix: `_fold_lines` unwraps optional NODE payloads the same way, and both fold walkers are
regenerated. That covers every optional node child in `hir_visitor.spl` and `ast_visitor.spl`:
ArrayLit/ArrayRepeat/DictLit element types, optional `else` blocks and optional values. The
pin is `hir_generated_optional_child_spec` "fold walker source unwraps the optional ArrayLit
element type" (fails on the old output, passes on the new).

Two earlier hypotheses were disproven by CI and dropped (PR #4235, closed): first rewriting the
nested optional if-expression that builds `elem_type` as statements (run 39963503260), then
building the default `HirType` at the use site with the live span (run 39969828508). Both still
SIGSEGVed at the same PC.

### Update 2026-10-24: after the fold-walker fix, receiver gate fails on env restore (same Some-box class)

With #4237, Stage 2 sanity passes on x86_64 Linux (CI run 39978925070), and the struct receiver
guard passes. The positional dynload route on this fixture no longer SIGSEGVs, but it fails with
`error: could not restore native-build cache environment` (`bootstrap_main.spl:455`). I reproduced
this locally with the receiver-rejected candidate from CI run 39994046780. gdb shows
`native_build_cache_restore(previous: text?)` receiving a `Some` box (header
`0x0000001800000007`/`0xf198715900000001`, text pointer at +16). After `if previous == nil:
return ...`, native Stage 2 passed the box itself to `sosix_env_set`. `sosix_admit_c_string`
refused it, and `rt_env_set` was never called for the restore. Without an inherited
`SIMPLE_NATIVE_BUILD_CACHE_DIR` the restore takes the remove branch and succeeds, which is why the
sanity battery's positional probe passed.

Fix: explicit `if val present = previous:` unwrap in `native_build_cache_restore` and
`native_build_output_mode_restore`, marked against
`optional_array_payload_narrowing_native_2026_10_21` (the same narrowing gap, applying to `text?`
as well as arrays). Other `if x == nil: return` followed by using `x` as `T` sites are likely
exposed the same way; they have not been audited.
