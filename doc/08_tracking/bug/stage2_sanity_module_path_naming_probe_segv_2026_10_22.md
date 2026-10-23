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
class-field layout/copy for large inline structs. (Landed 2026-10-23 as PR
#4172 d700e18bf00 — the sanity probe now passes.)

## Update 2026-10-23 (stage-2 sanity PASS; route probe still SEGVs, MIR phase)

With PR #4172 (flatten) + PR #4185 (reverse-reference publish scalar
mirror) merged on release/1.0.0, the full stage-2 SANITY battery passes:
`stage2-sanity.env status=pass checks_run=5`, both bootstrap passes, all
four probes (p2_add, mir_retention, module_path_naming, hello_world)
raw_status=0. The struct-receiver guard probe also passes (build + run,
exact stdout). The remaining blocker is the probe's SECOND admission, the
positional dynload Stage-3 route:

```
bootstrap_stage2_struct_receiver=PASS
... line 157: Segmentation fault ... "$stage2_compiler" native-build \
    --mode dynload ... stage2_module_path_naming.spl
error: stage2 failed the positional pure-Simple Stage-3 route (status 139)
```

Crash bracket: after HIR (`phase=hir done=1 succeeded=1`,
`any-escape pass: 0 diagnostic(s)`) — at MIR-phase entry. Reproduced
manually against the rejected candidate in ~4 s, DETERMINISTIC and
ENV-INDEPENDENT (a plain `candidate native-build --mode dynload
--threads 1 -o out <fixture>` with no probe env SEGVs identically).

Bisection matrix (candidate, cold cache): one-binary+positional PASS;
dynload+`--entry` flag PASS; dynload+positional p2_add PASS; only
dynload+positional+THIS fixture SEGVs. Fixture minimization (header
comment removable; 7 functions): no single function crashes; the pair
`_module_path_naming_tier_inner_twin` × `_module_path_naming_strip_numbered_dirs`
SEGVs; `text_index_of` is irrelevant. The interaction site is strip's
call `tier_inner_twin(stripped_part, parts[parts.len() - 1])`, but the
sanctioned annotated-rebind workaround (`val last: text = parts[...]` then
pass `last`) DOES NOT rescue it — the trigger is deeper than the
array-element-argument family (same conclusion shape as this doc's
earlier "local binds do NOT rescue" finding for the class field).

The sibling release/1.0 lane carries byte-identical fixture, probe, and
module_path_naming sources — no fix exists on either branch. Next step
for the fixing lane: symbolized backtrace of the MIR-phase fault (cdb was
unavailable in the 2026-10-23 session; WER produced no dump for the
msys-spawned child) or per-helper env-gated traces at MIR lowering entry.


## Addendum 2026-10-22 (Kimi session, appended; earlier observation, different crash site)

Observed BEFORE the definitive class-large-struct-field root cause above was
isolated, on a cranelift stage-2 candidate for this same fixture; kept for
cross-reference because it brackets a SECOND fault moment in the same lane.
Reproduced with the stage-2 candidate directly
(`simple.rejected native-build --backend=cranelift --runtime-bundle
core-c-bootstrap --entry-closure --entry
src/compiler/bootstrap_admission/stage2_module_path_naming.spl`, `ulimit -c
unlimited`, core captured). Worker argv confirms it runs
`src/app/cli/native_build_worker.spl --hir-shard=0/1`; backtrace (gdb,
bottom-up, all frames in `compiler.hir.generated.hir_codec`):

```
#0  hc_enc_hir_expr_kind
#1  hc_enc_hir_expr
#2  hc_enc_hir_block
#3  hc_enc_hir_if_arm
#4..#20 (encode recursion through expr/stmt/block/if_arm/function/module)
#21 hir_module_encode
#22 hir_module_decode_stable        <- called from the store selfcheck roundtrip
#23 driver_hir_cache.hir_cache_store_in_owned_scope
#24 driver_hir_cache.hir_cache_store
```

So this worker SEGSEGV'd while ENCODING an HIR expression node (the encode
recursion descends through an `if_arm` — the fixture's `collapse_inner_repeat`
boolean chain is the densest if-nesting in the file), reached from the
hir-cache store selfcheck roundtrip. If the class-field corruption above
malforms the HIR before this point, the encoder is where the corruption
becomes a fault — consistent with the definitive root cause rather than a
separate defect. Implication: any lane that lowers this fixture shape with
the hir cache enabled dies in `hir_cache_store`; a cache-disabled run only
survives until the next consumer of the same malformed node.
