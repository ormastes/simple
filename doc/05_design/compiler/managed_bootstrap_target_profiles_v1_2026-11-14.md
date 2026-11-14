# Managed bootstrap target profiles

Status: managed source implementation and bounded native policy projection
verified; no full bootstrap qualification or new XRay capability claimed. This applies to newly created managed jobs, never mutation
of a running/frozen bootstrap.

Phase 3 selects Development (`debug`/`dev`); phase 4 selects Release
(`release`/`prod`). This is the target artifact's profile. Producer path/digest
remain independent admission facts. Default optimization is respectively 0/2;
optimization never determines the target profile.

The approved shared owner is `compiler.common.driver_compile_options`:
`TargetBuildProfileV1`, `TargetDebugRequestV1`, `TargetTraceCapabilityV1`,
`TargetTraceResolutionV1`, `NormalizedTargetProfileV1`. Managed callers set
`managed_build_phase` and use `compileoptions_target_profile_v1` with the driver
capability resolver. Ordinary development callers retain their old default.

Phase-3 Default requests debug instrumentation automatically. Current absence
of an admitted provider resolves to Unavailable with the shared stable reason;
it does not emit instrumentation or claim activation. Explicit Enabled fails
when unavailable. Phase 4 resolves Disabled and forbids XRay. The actual backend
admission remains closed until its separate qualification is complete.

Managed compiler argv carries `--profile=dev|prod` and
`--managed-build-phase=phase3|phase4`. The compiler owns validation of these
selectors. A producer that does not recognize them must fail, never silently
accept the previous both-release semantics. The direct phase-4 wrapper binds
the same selectors in its execution argv and argument digest; its BUILD_ONLY
receipt advances to format 2 with explicit profile fields.

Index variants add managed phase and an explicitly absent trace-admission
identity, plus the shared schema/profile/request/resolution/reason fields.
Existing target/backend and optimization fields remain in the key. An Available
result is rejected by this index path until it can bind a real admission receipt
identity. No capability is inferred from a backend name or compile flag.

Creation, phase2/provisional authority verification, index readback verification
and grouped preparation all rederive the typed profile. Old phase-3 release
variants, phase-4 development variants, and pre-schema phase-4 variants fail
admission even when their old hashes are internally valid. Retained job argv
comparison rejects old binary manifests. New private output roots are required;
no stale job is silently resumed or rewritten.

Validation plan: actual variant tests cover normalized fields, round-trip
admission, phase conflicts and stale schema. Check generated command selectors,
argument digest agreement and shell syntax. Full compiler/bootstrap execution
is separate required qualification; authored tests alone are not a pass.

## Retained verification evidence

The admitted pure-Simple producer SHA
`855f48d3c9f9d915be2c8d732d4da3186caa0fb49f55ba3c780a47a1bb7efd42`
compiled exact shared CompileOptions/defaults, managed variant/admission
functions, canonical ConfigVariantKey encoding and the actual SHA implementation.
The frozen fixture `bd4077d26235473b057af836c899cf275aa4f1f9` passed 30 native
scenarios: twelve target/backend/phase combinations with typed round trips and
profile-separated digests, twelve phase/profile mismatch rejections, and six
old-schema receipt rejections. An external SHA-256 known answer was checked.
Compile and execution exited zero under a 2 GiB cgroup, one worker and a 120-second
compile bound. This executes a production-function projection, not manager I/O
or complete bootstrap jobs. Actual integration SSpec execution remains UNRUN.

Two earlier fixture extraction errors were retained: a truncated multiline
signature and unintended inclusion of SSpec DSL. Neither is reported as a
product defect. The corrected extraction verified 35 added declaration spans
and 26 shared declarations byte-for-byte against their sources before compiling.
Artifacts: `/tmp/managed-profile-native-20261114/` (source hashes, preflight,
three compiler logs and native execution log). Both edited shell scripts passed
syntax checks. Receipt/index consumer wiring was source-reviewed; it was not
represented as a completed persisted-resume experiment.

## Managed command coherence followup

Grouped artifact commands derive `--opt-level=none|standard` from the admitted
phase/backend/target index and reject missing, duplicate or inconsistent values.
Direct phase-4 commands and their argument digest explicitly select standard.
Both paths transport `--low-memory`. Debug information retains the ordinary
CompileOptions default (true), independently of release debug-aspect removal.
The index describes native module artifacts; ordinary dynload binary packaging
remains Both, recorded as such in the direct-product receipt. These are distinct
artifact identities, not interchangeable cache variants.

The exact shell selector passed nine positive/negative cases and two optimization
wiring assertions; two additional low-memory wiring assertions passed separately.
A focused native projection passed two new phase3/phase4 debug-info, optimization
and low-memory scenarios, without repeating the earlier 30 cases. Its shared
declarations are pinned to c065340a279 and managed declarations to the followup
source snapshot. A preflight initially compared the older shared projection to
newer owner source and failed; a missing shell fail-fast allowed compilation to
complete before the owned scope was stopped. Before executing the artifact, all
26 shared declarations were verified against c065340a279 and all 35 added spans
against their exact sources. No product defect or full-manager pass is inferred.
Artifacts: `/tmp/managed-profile-followup-20261114/`; full bootstrap remains UNRUN.
