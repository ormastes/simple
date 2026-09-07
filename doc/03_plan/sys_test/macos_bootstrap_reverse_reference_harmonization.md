<!-- codex-design -->
# SPipe Plan: macOS Bootstrap Reverse-Reference Harmonization

Status: MBH-NFR-002 executable coverage implemented; cross-architecture native
qualification remains governed by the wider M4 plan.

## Shared scenario and checker names

Manual steps are exactly: `step("Build the native thin compiler lane")`,
`step("Publish ReverseReferenceKeyV1 projection receipts")`,
`step("Attempt compatible Phase 2 to Phase 3 reuse")`, and
`step("Compose and admit the universal candidate")`.

Checker helpers are exactly:

- `check_reverse_reference_key_v1_frame`
- `check_reverse_reference_projection_receipt`
- `check_macos_bootstrap_receipt_v1`
- `check_phase_compatibility_manifest`
- `check_native_macho_slice_receipt`
- `check_full_cli_test_runner_build_receipt`
- `check_producer_bound_cache_identity`
- `check_universal_promotion_without_rebuild`

Unimplemented helpers must call `fail(...)`; they must never silently return.

## Planned coverage and traceability

| Requirement | Evidence class | Planned scenarios |
|---|---|---|
| MBH-REQ-001/002/008 | live native macOS runners | thin Phase2/3 startup, focused compile/test, CLI/MCP/LSP, mismatch rejection |
| MBH-REQ-009 | live native macOS runners plus cache receipts | Phase2 and Phase3 each complete full CLI and test-runner builds inside exact-producer-bound caches on both architectures; reject unbound, mismatched, shared-writable, or substituted producer caches |
| MBH-REQ-003/004/006 | host fixture plus native integration | stable framing, exact consumers, unknown/corrupt generation fallback, mutation-red encoder |
| MBH-REQ-005 | integration | separate writers, read-only manifest admission, wrong producer/provider/target/schema rejection |
| MBH-REQ-007 | live native macOS runners | two admitted slices, `lipo`, per-slice hashes, native execution, promote-without-rebuild |
| MBH-NFR-001..006 | receipts and repeated runs | normalization equality, zero-work no-op, 20 warm requests, writer/crash/GC matrix |

MBH-NFR-002 is additionally traced to
`test/03_system/compiler/feature/native_zero_work_admission_spec.spl` and
`test/03_system/app/compiler/feature/macos_reverse_reference_m4_native_qualification_spec.spl`.
Its cases cover a true native-build warm hit, zero actual phase scheduler
counters, canonical invocation/input mismatches, immutable-name collision
recovery, deleted/corrupt ancestry, and process death before/after generation
and `CURRENT` renames. The native executable is required; absence or a rejected
runtime is `BLOCKED`, never a synthetic pass.

Planned executable location:
`test/03_system/compiler/bootstrap/macos_bootstrap_reverse_reference_harmonization_spec.spl`.
Planned generated mirror:
`doc/06_spec/03_system/compiler/bootstrap/macos_bootstrap_reverse_reference_harmonization_spec.md`.
The manual is deferred until an executable spec exists so docgen does not
mistake a documentation skeleton for generated evidence.

Pass requires native evidence from both architectures, full CLI and test-runner
builds in exact-producer-bound Phase2/3 caches, stable reason codes, real
`Results:` output, and all negative/mutation fixtures going red. Source string
checks, translated execution, unbound or mismatched cache artifacts, and
Rust-seed artifacts are insufficient.
