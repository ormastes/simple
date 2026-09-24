# MacOS Reverse-reference M5 Universal Packaging And Promotion

- Executable: `test/03_system/app/compiler/feature/macos_universal_m5_spec.spl`
- Requirements: `MBH-NFR-004`, `MBH-NFR-005`, `MBH-REQ-001`, `MBH-REQ-007`, `MBH-REQ-008`, `MBH-REQ-009`
- Evidence class: executable SPipe definition; no execution summary is embedded.

## Scenarios
- keeps portable qualification hermetic and distinct from native release proof.
- retains exact provenance and requires post-sign native CAS authority.

## Manual Steps
- run M5 from a digest-bound immutable snapshot; leave native signing and promotion blocked.
- Retain each complete M4 tree under its evidence-manifest digest, bind child
  execution to the candidate, recompute canonical policy, require native
  post-sign checks on both architectures, and CAS-promote with a rollback receipt.

## Selected Policy
- Universal promotion requires exact authenticated M4 run/workflow/artifact
  identities, retained arm64 and x86_64 M4 trees, real Apple signing/notary
  evidence, two post-sign native PASS receipts, and an expected-current CAS.

## Freshness
- Requirement IDs and scenario names mirror the executable source as of 2026-09-02.
- The executable contains no `pass_todo` or tautological `expect(true).to_equal(true)` evidence.
- Runtime execution was not available in this audit because the admitted self-hosted `bin/simple` lacks `test`; no runtime PASS is claimed.
- Native post-sign and rollback execution remain `BLOCKED`; portable mutation
  evidence exercises structure only and cannot authorize release.
