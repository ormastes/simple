# Typed collection physical-plan acceptance

This is an authored manual for `test/03_system/app/compiler/feature/profile_switchable_typed_plan_acceptance_spec.spl`. SPipe execution and generation have not run on an admitted Stage 4 runtime. The scenario intentionally ends with `MissingEvidence` until a production physical-decision receipt exists; it cannot be reported as PASS.

The suite entry invokes canonical `stage4_verify_candidate_provenance` once for the exact executable, its `.provenance.env`, and this source tree. It retains accepted candidate, provenance and source hashes under `build/test-artifacts/stage4-source-admission-<pid>.txt`; the scenario rechecks candidate and receipt hashes before workload capture.

The runner needs `sh` on `PATH` (the Git POSIX shell on Windows). If it is absent, admission fails MissingEvidence before compilation.

1. **Prepare attributed containers.** Admit a source-matched pure-Simple compiler with stub fallback disabled. Keep the canonical fixture and output paths tied to this run.
2. **Capture workload profile.** Run the actual collection probe with source module identity, workload and target; require its profile artifact and logical PASS marker.
3. **Admit profile for same site.** Supply the captured profile, same source, same workload and target to the native build.
4. **Compile and execute selected representation.** Build the fixture with LLVM and execute the resulting artifact. Require successful compilation and its logical PASS marker. Preserve command output under `build/test-artifacts/compiler/typed-physical-plan-<pid>.txt`.
5. **Verify logical results and selection evidence.** Require a versioned production receipt for the exact typed site, source, target, backend, workload, profile epoch, selected representation, guard/rejection and memory facts, and lowered MIR loop/index identity, bound to this artifact. Compare native logical results with the reference behavior. The current compiler does not emit this receipt, so the executable spec fails explicitly instead of treating advisory explanation text as proof.

The group item 7 owner and item 3 physical-planning owner will finalize the receipt schema and CLI path. Update the executable assertions and regenerate this manual only when that production route exists and an admitted compiler can execute it. The current fixture demonstrates the intended input/output path; it does not yet establish an optimizer-to-MIR decision.
