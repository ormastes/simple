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

## Update 2026-10-22 (later): crash now universal on the convergence head; optional-field dodge insufficient

On 244f807d029 (post release/1.0 convergence merge) the same projection fault
fires for EVERY probed module, including p2_add and a one-line hello-world —
not only the path-naming fixture. Symbolized worker backtrace on the current
candidate:

```
#0 module_surface_semantic_projection (+~6100; fault: mov 0x8(%rax),%rdi with
    rax pointing into ASCII text -- a ParserModule field read as a list header
    lands on text bytes, consistent with a shifted/garbage module copy)
#1 module_surface_from_owner
#2 ModuleSurfaceBuilder.add_parsed_canonical
#3 CompilerDriver.parse_all_impl
```

Attempted and REJECTED by experiment: making the owner field optional
(`value: ParserModule?`, keeping the class slot pointer-sized) so no large
inline struct field remains — the crash persists unchanged at the same site.
The corruption therefore survives removing the inline-struct class field, so
the class-field layout read is at most one member of the failing family; the
by-value arg transport into the projection and/or the enum-payload extraction
(`unwrap`) of a large struct remain suspect.

Control experiment: the identical owner->from_owner->projection path compiled
by the Rust seed into a 284-module probe binary runs cleanly
(`module_surfaces_from_modules` returns OK on a parsed hello-world). The
failure only appears in the full ~1487-module stage-2 candidate — a
scale-dependent seed/native-lowering miscompile, not a source-level logic
error in the surface code.

Host note: all evidence above is from the Linux LLVM-23.1.2 lane on a
7.6 GiB host; the phase-matrix `compiler_cli_build` separately exceeds the
process-tree RSS cap there (~5.3 GiB measured, cap 5.59 GiB) and is reported
as TIMEOUT — that row cannot complete on this host class regardless of this
crash.
