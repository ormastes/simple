# Typed collection physical-plan acceptance

This is an authored manual for `test/03_system/app/compiler/feature/profile_switchable_typed_plan_acceptance_spec.spl`. SPipe execution and generation have not run on an admitted Stage 4 runtime. The profile-replay scenario intentionally ends with `MissingEvidence` until an artifact-bound production physical-decision receipt exists; the suite cannot be reported as PASS.

## Literal membership guard and execution scenario

The separate literal scenario uses the three-entry duplicate-key fixture at
`test/fixtures/profile_switchable/typed_literal_membership_probe.spl`. It requires
Original at O0, zero budget, or the malformed explicit target `x86_64-madeup`,
and a consumed Linear MIR decision at O2 with a
512-byte scratch budget on the explicitly requested x86_64 Linux target. The
consumed decision must retain the insertion-failure fallback. It then runs the
same fixture through the interpreter and an LLVM native build for the actual
host, checks the PASS marker and matching output, and rechecks source/compiler
hashes. Every child is bounded and output is retained incrementally under
`build/test-artifacts/compiler/literal-membership-<pid>.txt`.

This proves separate MIR-guard and logical-execution criteria when run; it does
not bind the Linux explanation to the host native artifact or discharge the
profile-replay requirement below. Status: authored, NOT RUN.

## Profile replay and artifact-bound selection scenario

Local implementation update: standalone native builds with an explicit collection
memory budget now have a `.collection-plan-receipt` publication path. It binds
current admitted module capsules, report digests, object digests, build request,
and final artifact bytes. This is linked-input MIR evidence, not proof of runtime
equivalence, linker retention, or profile-driven selection. Zero-report builds
are labeled `no-reported-plans`; grouped publication remains unsupported. The
integrity/ownership unit cases are authored but NOT RUN. The profile scenario
below still lacks its required profile/site/epoch-to-executed-representation
evidence and must not be marked passing on the strength of this partial receipt.

The October 4 source review additionally found that the linker consumes mutable
object paths: before/after digests do not prove which bytes it read. Until owned
immutable admitted inputs replace those paths, the sidecar is diagnostic only.
See `doc/08_tracking/bug/collection_native_mutable_link_inputs_2026-10-04.md`.

The suite entry invokes canonical `stage4_verify_candidate_provenance` once for the exact executable, its `.provenance.env`, and this source tree. It retains accepted candidate, provenance and source hashes under `build/test-artifacts/stage4-source-admission-<pid>.txt`; the scenario rechecks candidate and receipt hashes before workload capture.

The runner needs `sh` on `PATH` (the Git POSIX shell on Windows). If it is absent, admission fails MissingEvidence before compilation.

1. **Prepare attributed containers.** Admit a source-matched pure-Simple compiler with stub fallback disabled. Keep the canonical fixture and output paths tied to this run.
2. **Capture workload profile.** Run the actual collection probe with source module identity, workload and target; require its profile artifact and logical PASS marker.
3. **Admit profile for same site.** Supply the captured profile, same source, same workload and target to the native build.
4. **Compile and execute selected representation.** Build the fixture with LLVM and execute the resulting artifact. Require successful compilation and its logical PASS marker. Preserve command output under `build/test-artifacts/compiler/typed-physical-plan-<pid>.txt`.
5. **Verify logical results and selection evidence.** Require a versioned production receipt for the exact typed site, source, target, backend, workload, profile epoch, selected representation, guard/rejection and memory facts, and lowered MIR loop/index identity, bound to this artifact. Compare native logical results with the reference behavior. The current compiler does not emit this receipt, so the executable spec fails explicitly instead of treating advisory explanation text as proof.

The group item 7 owner and item 3 physical-planning owner will finalize the receipt schema and CLI path. Update the executable assertions and regenerate this manual only when that production route exists and an admitted compiler can execute it. The current fixture demonstrates the intended input/output path; it does not yet establish an optimizer-to-MIR decision.
