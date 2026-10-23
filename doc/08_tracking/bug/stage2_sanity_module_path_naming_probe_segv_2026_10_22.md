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

## Addendum 2026-10-23 (Kimi session, riscv64 guest lane): same family, failure moved past surface_build into HIR scope end

Cross-test lane (`check-linux-riscv64-bootstrap-qemu.shs --cross-test`, QEMU
riscv64 TCG guest, 24 vcpu, glibc 2.39) on the rebased release tree
(`release/1.0.0` head 963358b7f31, which merged the ModuleSurfaceParserOwner
flatten `d700e18bf00` + parser-alias reroute `7183b3e1f44` +
typed-bind-before-alias-walk `dd77408774`): the phase-1 cross-built
self-hosted compiler (`build/cross/linux-riscv64/simple`, 1487 units, 0
failed) runs fine (`--version` -> `simple-bootstrap 1.0.0-rc.1`, RC=0), but
`native-build build/sanity/hello.spl` now fails DETERMINISTICALLY (reproduced
twice, ~21-26 s into the build, before the earlier surface_build SEGV site is
even reached as a crash — the lane progresses through parse/surface_build/
surface_alias/export_origins/surface_freeze and dies in phase 3):

```
[bootstrap-error-count] source_idx=0 point=entry count=0
[ERROR] phase 3 FAILED
[ERROR]   transient HIR scope end failed for build/sanity/hello.spl
error: in-process native-build: transient HIR scope end failed for build/sanity/hello.spl
```

Interpretation: consistent with the definitive root cause documented above
(class-with-large-struct-field read returns garbage). The upstream surface/
parser-owner refactor changed WHERE the malformed state first trips a
checked path — the HIR transient-scope end now catches the corruption and
fails gracefully instead of the earlier lane SEGV'ing inside surface_build.
Same family, different tripwire; the riscv64 guest remains a reliable
reproducer for whatever lane owns the fix. Not caused by the riscv64
cross-lane fixes (seed externs / link knob / rootless debs) — those only
affect producing the ELF and the host-side test runner.

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

## Update 2026-10-22 (flatten attempt): prescribed flatten also insufficient — transport corruption is upstream of the owner

The prescribed flatten was implemented: ModuleSurfaceParserOwner now carries
only pointer-sized fields (one text/list/Dict handle per ParserModule limb),
the class moved to module_surface_types.spl, the projection and the
objectless-proof consumers read owner fields directly, and no ParserModule is
extracted from the class. The worker STILL SIGSEGVs with an identical
backtrace (projection reading owner.impls lands on text bytes), so the
corruption is already present in the by-value ParserModule argument handed to
ModuleSurfaceParserOwner.new / add_parsed_canonical — i.e. the large-struct
by-value ARGUMENT transport corrupts at stage-2 scale, before any class field
is involved. This matches the NLL live_aliases instance (fixed by moving the
callee to module scope), but here every hop is already a free function, so the
remaining suspect is the seed's by-value aggregate argument marshal itself in
the ~1487-module candidate.

The flatten is retained anyway: it matches the prescribed direction, compiles
cleanly, and shrinks the corruption surface, but it does NOT fix the crash.
Effective next step is therefore NOT another caller-side reshape: reproduce a
large-struct by-value argument in a seed-built binary whose module count
crosses the failing threshold, or compile the candidate with -g and read the
exact faulting field offset in the marshal path.

## Note 2026-10-23 (sync of release_phase3 into release/1.0.0)

Both branches carried an independent `ModuleSurfaceParserOwner` flatten
(release: d700e18bf00 + c458ffe5cbc; release_phase3: 4417cdb92e6 + ab4b33d2404).
The sync keeps the release version and drops the duplicate. The
release/1.0.0 line also carries #4151 (f6cec219135): `rt_transient_heap_promote`
(Rust twin) returned true for ANY registered heap root, so the retained parse
`Result<ParserModule>` was freed at scope end and `surface_build` read freed,
reused memory (the "ASCII text in a ParserModule field" symptom above). With
#4151 the riscv64 lane gets past surface_build and stops at the next tripwire,
"transient HIR scope end failed" (addendum above).


## Located 2026-10-23: SIGSEGV is in the HIR codec encoder, via the cache store

Next step 1 above is done. The crash is **not** the
`self.method(array_arg, ...)` argument-corruption family this record
hypothesised, so steps 2 and 3 as written do not apply to it.

### Fast reproduction — ~110 ms, no bootstrap

```sh
R=.simple/storage/build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple.rejected
env -u SIMPLE_BOOTSTRAP CAP_MEM_MAX=4G sh scripts/resource/run_capped.shs \
  "$R" native-build --runtime-bundle core-c-bootstrap --entry-closure \
  --entry src/compiler/bootstrap_admission/stage2_module_path_naming.spl -o /tmp/probe
# worker terminated with signal 11, during phase=hir
```

### gdb recipe (the two things that make it work)

```sh
# 1. capture the worker argv -- -s must be LARGE or the base64 policy arg is
#    truncated and the worker answers `invalid-internal-argument:corrupt`
strace -f -qq -s 60000 -e trace=execve -o /tmp/st.log "$R" native-build ...
# 2. SIMPLE_NATIVE_BUILD_WORKER=1 is REQUIRED: without it the bootstrap CLI
#    answers `unknown command 'run'` (bootstrap_main.spl:629 gates the
#    internal `run` entry on that marker).
env -u SIMPLE_BOOTSTRAP SIMPLE_NATIVE_BUILD_WORKER=1 \
  gdb -q -batch -ex run -ex 'bt 40' --args <argv from step 1>
```

### Backtrace — 35 frames, bottoming out at `main`

```
#0  compiler.hir.generated.hir_codec.hc_enc_hir_expr_kind   <-- SIGSEGV
#1  hc_enc_hir_expr
#2  hc_enc_hir_block
#3  hc_enc_hir_if_arm
#4  hc_enc_hir_expr_kind
...  expr -> stmt_kind -> stmt -> block -> expr_kind recursion
#19 hc_enc_hir_function
#20 hc_enc_hir_module
#21 compiler.hir.hir_codec.hir_module_encode
#22 compiler.hir.hir_codec.hir_module_decode_stable
#23 compiler.driver.driver_hir_cache.hir_cache_store_in_owned_scope
#24 compiler.driver.driver_hir_cache.hir_cache_store
...
#33 spl_main
#34 main
```

**It is not stack exhaustion.** The whole stack is 35 frames and terminates
normally at `main`; the recursion visible in frames 0-20 is just the HIR tree
walk. This is a bad-pointer dereference inside `hc_enc_hir_expr_kind`.

### Mechanism

`hir_cache_store` encodes the module, then verifies round-trip stability
(`hir_codec.spl:555`):

```simple
fn hir_module_decode_stable(blob: text) -> HirModule?:
    val decoded = hir_module_decode(blob)
    if decoded == nil:
        return nil
    if hir_module_encode(decoded.unwrap()) != blob:   # <-- crashes here
        return nil
    decoded
```

`hir_module_decode` returns a **non-nil** `HirModule` that is not safely
encodable, so the stability check segfaults instead of answering `nil`. The
defect is therefore incomplete decode validation: `decode` admits a blob that
produces a structurally invalid expr-kind payload. Note the shape of the
failure — `decode_stable` exists precisely to catch an unstable round trip, and
it cannot, because re-encoding the bad tree crashes before the comparison.

Owner note: `src/compiler/20.hir/generated/hir_codec.spl` is GENERATED (8,807
lines); the fix belongs in the generator and/or in `decode`'s validation, not
in hand edits to that file.

### Ruled out, with evidence

- **Not the method-call argument family.** The backtrace never enters the
  fixture's own code; it crashes in the codec during cache store, after HIR
  lowering has already completed clean (`[bootstrap-error-count] ...
  point=post-lowering count=0`, `point=post-diagnostics count=0`).
- **`SIMPLE_HIR_CACHE=0` is NOT a usable workaround.** With the shard argument
  present the worker then fails closed with `HIR cache identity unavailable for
  shard`; without sharding the SIGSEGV simply moves. The shard lane requires
  cache identity, so the cache cannot be switched off to get past this.
- **The reverse-reference batch is healthy here.** A probe in `publish` on the
  same run reports `field_token=1 mirror_token=1 field_gen=1 field_sealed=true
  field_valid=true`, so the batch-promotion defect fixed in #4202 is not
  implicated in this crash.

### Revised next steps

1. Find which `HirExprKind` variant `decode` admits with an invalid payload —
   encode/decode the fixture's module in isolation and bisect by variant.
2. Make `hir_module_decode` reject it (fail closed) so `decode_stable` answers
   `nil` instead of crashing; that alone restores a clean cache miss.
3. Then fix the generator so the variant round-trips.

## 2026-10-23: the nil-scalar-reject fix does NOT close this bug (measured)

`68bb9e04ed5` ("fix(codec): restore generator parity; fail closed on nil in
non-optional scalar slots") landed the hypothesis that this SIGSEGV comes from
`hir_module_decode` admitting a blob that stores the wire nil sentinel in a
non-optional scalar slot (e.g. `IntLit.value: i64`), so that re-encoding the
decoded node faults. Its commit message states **"Stage 2 re-run still
pending."**

**That re-run has now been done, and the SIGSEGV is unchanged.** The same change
(non-optional `i64`/`bool` rejecting the nil sentinel, 161 emitted reject sites
in the variant measured here; the landed commit has 231 including `text`) was
built into a Stage 2 candidate and the sanity battery still fails identically:

```
candidate_frontend_smoke: stage2-module-path-naming-build failed
[hir-shard] owner=0/1@0 status=CRASH exit=-139
```

gdb against that candidate gives the same stack as before the change:

```
#0  compiler.hir.generated.hir_codec.hc_enc_hir_expr_kind   <-- SIGSEGV
...
#21 compiler.hir.hir_codec.hir_module_encode
#22 compiler.hir.hir_codec.hir_module_decode_stable
#23 compiler.driver.driver_hir_cache.hir_cache_store_in_owned_scope
#24 compiler.driver.driver_hir_cache.hir_cache_store
```

So the nil sentinel is **not** the source of the unreadable payload. The
fail-closed change remains defensible as hardening — a non-optional slot should
never decode to nil — but **this bug must not be closed on it**, and the
decoder's nil-sentinel handling is no longer a live lead.

### Hypotheses now disproved, with their disproofs

| hypothesis | disproof |
|---|---|
| method-call argument corruption (`self.m(array, …)`), this record's original next-step 2 | the backtrace never enters the fixture's code; HIR lowering completes clean (`post-lowering count=0`, `post-diagnostics count=0`) |
| `SIMPLE_HIR_CACHE=0` as a workaround | with the shard argument the worker fails closed with `HIR cache identity unavailable for shard`; without sharding the SIGSEGV moves rather than disappearing |
| nil sentinel in a non-optional scalar slot (`68bb9e04ed5`) | built into a Stage 2 candidate; SIGSEGV unchanged, same route and same frame |

### What the open question actually is

`hir_module_encode` succeeds on the live module (the store gets a non-empty
blob), and fails on the module that `hir_module_decode` returns from that same
blob. The encoder's own node guards (`nil` / `rt_heap_ref_wellformed` /
`rt_heap_ref_registered`) all pass, and the fault is in
`hc_enc_hir_expr_kind`'s own frame — so a payload slot of a node that looks
well-formed and registered is unreadable. The remaining question is what leaves
a slot in that state when the node came from `decode` rather than from lowering.

### Two facts about the regeneration that neither commit records

- **A third wire-format change.** `HirStmtKind.Assign.op` is declared
  `HirAssignOp?` (`hir_definitions.spl:801`) but the pre-regeneration output
  encoded it as a non-optional node. Regeneration adds the optional layer, so
  every compound assignment's bytes move. Encoder and decoder agree, so this is
  not corruption, but a reader diffing v9 against v10 blobs needs it.
- **Four codec round-trip examples already fail** on `release/1.0.0`, unrelated
  to any of this: `hir_codec_integer_three_spec` (executed=7 passed=5 failed=2)
  and `hir_codec_optional_node_bare_spec` (executed=3 passed=1 failed=2), with
  byte-identical counts against origin's v9 codec. Worth their own record.

### `push-hir-codec-complete` passes now, and should stay advisory

With generator parity restored the pre-existing gate passes:
`PASS — 97 declaration(s) covered, generated codec fresh`. It should NOT be
promoted to blocking: it resolves `SIMPLE_BIN="${SIMPLE_BIN:-$ROOT/bin/simple}"`
and exits 2 without one (`ERROR — nothing was checked`), which
`.claude/rules/vcs.md:246-251` records as exactly why `push-dual-run-shadow` is
advisory — a blocking row would refuse every push from a binary-less host. Its
real gap is that it appears in no `.github/workflows/` file, so it has no CI
lane either; that is what let generator parity drift unnoticed.
