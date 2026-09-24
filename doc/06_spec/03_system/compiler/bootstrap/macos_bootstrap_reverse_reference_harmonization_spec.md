# macOS Bootstrap Reverse-Reference Harmonization

- Executable: `test/03_system/compiler/bootstrap/macos_bootstrap_reverse_reference_harmonization_spec.spl`
- Requirements: `MBH-REQ-001`, `MBH-REQ-002`, `MBH-REQ-003`, `MBH-REQ-004`,
  `MBH-REQ-005`, `MBH-REQ-006`, `MBH-REQ-007`, `MBH-REQ-008`, `MBH-REQ-009`,
  `MBH-NFR-001`, `MBH-NFR-002`, `MBH-NFR-003`, `MBH-NFR-004`, `MBH-NFR-005`,
  `MBH-NFR-006`
- Evidence class: executable structural umbrella; no native result is embedded.

## Scenarios

- keeps M0 and M1 structural evidence separate from native admission
- binds M2 projection receipts to the canonical framed key
- keeps M3 compatible reuse fail closed under receipt drift
- keeps M4 and M5 native qualification blocked without retained native evidence

## Manual Flow

- Build the native thin compiler lane without treating portable structure as admission.
- Publish `ReverseReferenceKeyV1` projection receipts.
- Attempt receipt-bound Phase 2 to Phase 3 compatible reuse.
- Compose the universal candidate only from independently admitted native slices.

## Performance Authority

Each architecture requires its own admitted baseline receipt. Maximum steady
RSS is 110% of baseline RSS; nonnegative growth across 20 warm requests is 10%
of baseline RSS. The receipt binds architecture, baseline evidence, producer,
server, decision source, and requirements-document digests. Missing or stale
authority fails closed.

## Freshness

The requirement IDs and scenario titles mirror the executable source. The M4
and M5 native rows remain blocked; no runtime or native PASS is claimed.
