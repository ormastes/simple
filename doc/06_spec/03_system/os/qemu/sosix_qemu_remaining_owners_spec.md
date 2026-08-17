# SOSIX QEMU remaining-owner handoff manual

## Purpose and audience

This manual mirrors
`test/03_system/os/qemu/sosix_qemu_remaining_owners_spec.spl` for matrix owners
and reviewers. It proves fail-closed retention of incomplete rows; it never
promotes BLOCKED or POSTPONED rows to QEMU PASS. The executable spec remains
authoritative. A qualified Stage-4 runtime must regenerate this mirror before
runtime PASS is claimed.

## Preconditions

- Repository source and remaining-owner ledger at the same revision.
- Receipt-bound pure-Simple Stage-4 runtime; no Rust seed or Stage 2/3 reuse.
- Shared owner scripts executable from the repository root.
- Linked x86_32/ARM32/RV64 artifacts only when their admission scenarios are
  promoted beyond the current missing-artifact sabotage cases.

## Operator workflow

1. Validate the shared collector, media, and runtime owners.
2. Confirm aliased source/run media is rejected before mutation.
3. Confirm the admitted runtime identity is path/hash/version bound.
4. Exercise Linux lifecycle source gates and missing-linked-artifact rejection.
5. Compare all 24 retained rows with the canonical plan.
6. Confirm every incomplete lane retains its owner and unblock command.
7. Run docgen and `sspec-maintain scan` once with the admitted runtime.

## Scenario narratives

### Validate matrix promotion

`check-sosix-qemu-shared-owners.shs --self-test` must distinguish structural
bundle validity from all-24-row matrix promotion and bound captured output.

### Reject mutable source aliasing

Resolved source and run-media aliases reject before mutation. A distinct copy
may mutate without changing the source, and corrupted readback rejects.

### Bind the admitted runtime

Runtime identity is canonical path, SHA-256, and version bound. Missing,
stale, seed, and identity-mismatched inputs fail closed.

### Admit the Linux guest lifecycle

RV64 transport and x86_32/ARM32 lifecycle source gates execute. Deliberately
missing linked kernels must be rejected; this is not live guest evidence.

### Record unavailable native hosts

The oracle contains exactly 24 rows: 3 PASS, 15 BLOCKED, and 6 POSTPONED.
Those counts prove honest handoff state only.

### Retain the implementation handoff

Linux compiler/kernel owners, Windows/FreeBSD/macOS operators, and the
system-test/docgen owner remain explicit in tracking.

## Requirements and scorecard

| Requirement | Visible scenario | Evidence class |
| --- | --- | --- |
| REQ-SOSIX-QEMU-L0-001..003 | first three steps | host-fixture/source contract |
| REQ-SOSIX-QEMU-LINUX-OWNERS-001 | Linux lifecycle | source + linked rejection |
| REQ-SOSIX-QEMU-EXTERNAL-001 | 24-row oracle | retained non-PASS ledger |
| REQ-SOSIX-QEMU-HANDOFF-001 | implementation handoff | owner/resume documentation |

All scenarios contain concrete assertions. Machine docgen and seven-component
maintenance scores remain pending the qualified runtime.

## Findings and remediation

- Three Linux rows retain canonical PASS and must not be rerun unchanged.
- RV64, x86_32, and ARM32 remain blocked on admitted rebuild/live bundles.
- Windows and FreeBSD require native hosts; macOS remains postponed.
- The Stage-4 runtime absence blocks executable SSpec/docgen acceptance.

Resume only the named row/owner. Never relabel another host or substitute a
cached diagnostic transcript.

## Evidence and provenance

Retain the SSpec output, bounded script transcripts, runtime receipt/hash,
source revision, row ledger, and generated manual together. Fixture self-tests
are host-fixture evidence, not native-row bundles.

## Compatibility and limitations

The matrix stays exactly four real hosts by six guests. TCG is correctness
evidence only. A BLOCKED/POSTPONED expectation passing in this handoff spec
means the row was preserved and cannot be promoted; it does not satisfy its
native execution requirement.
