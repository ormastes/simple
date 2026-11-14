# Managed bootstrap target profiles

Status: implementation in progress; no bootstrap qualification or new XRay
capability claimed. This applies to newly created managed jobs, never mutation
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
