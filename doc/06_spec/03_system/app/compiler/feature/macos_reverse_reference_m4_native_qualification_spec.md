# MacOS Reverse-reference M4 Native Qualification

- Executable: `test/03_system/app/compiler/feature/macos_reverse_reference_m4_native_qualification_spec.spl`
- Requirements: `MBH-NFR-002`, `MBH-NFR-003`, `MBH-REQ-001`, `MBH-REQ-004`, `MBH-REQ-006`, `MBH-REQ-008`, `MBH-REQ-009`
- Evidence class: executable SPipe definition; no execution summary is embedded.

## Scenarios
- should run the production qualification checker's mutation-red self-test.
- should prove an actual unchanged native-build schedules zero compiler work.
- should reject an unavailable architecture rather than synthesize PASS.
- should reject prebuilt tool substitution before native qualification.
- should reject supplied provider archives and synthetic provider receipts.
- should reject residency qualification without an admitted architecture baseline.
- should bind qualification to authenticated Phase3 producer authority and canonical policy.
- should report BLOCKED for the non-native architecture before accepting artifacts.

## Manual Steps
- Execute the production M4 checker over all eight fixtures.
- Run the production native-build twice against one isolated identity and
  require the second invocation's real parser, HIR, MIR, codegen, and linker
  scheduler counters all to equal zero.
- Invoke the production checker with an invalid architecture mutation.
- Pass a helper path where M4 must build producer-bound tools itself.
- Pass a provider archive where M4 must build and trace a live archive itself.
- Inspect the production residency gate for an architecture-matched admitted
  baseline, steady RSS `<=110%`, 20-request growth `<=10%` of baseline RSS,
  and fail-closed missing-baseline behavior.
- Inspect the M4 producer authority for exact repository, workflow revision,
  head SHA, run attempt, artifact ID/digest, candidate digest, and admission
  digest bindings; recompute the selected kernel policy from `kernel_closure.sdn`.
- Select the architecture opposite to the current native host.
- Invoke the production checker without substituting cross-architecture evidence.

## Selected Policy
- Residency authority: baseline-relative 10%. Maximum steady RSS is `<=110%`
  of admitted baseline RSS; maximum 20-request growth is `<=10%` of baseline
  RSS. Missing baseline fails closed. Native residency qualification remains
  `BLOCKED` because no admitted baseline/measurement pair exists.

## Freshness
- Requirement IDs and scenario names mirror the executable source as of 2026-09-03.
- The executable contains no `pass_todo` or tautological `expect(true).to_equal(true)` evidence.
- Runtime execution was not available in this audit because the admitted self-hosted `bin/simple` lacks `test`; no runtime PASS is claimed.
- Authenticated Phase3 and native M4 artifacts remain `BLOCKED` until produced
  by the workflow on native arm64 and x86_64 runners.
