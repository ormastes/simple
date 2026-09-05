# SOSIX QEMU Matrix Contract Specification

| Tests | Active | Skipped | Pending |
|---:|---:|---:|---:|
| 12 | 12 | 0 | 0 |

The executable source is
`test/01_unit/os/sosix/qemu_matrix_contract_spec.spl`. It proves exact
four-host by six-guest completeness, uniqueness, receipt-derived PASS rows,
resume/ownership data for non-PASS rows, and aggregate blocking for postponed
macOS evidence. It also specifies the exact 41-scalar/9-artifact compiler-free
record, ordered literal artifact keys, canonical decimal encoding, policy
nonpromotion, identity binding, and manifest evidence-hash mismatch rejection.
Missing, duplicate, reordered, padded, forged, and malformed inputs fail
rather than disappear.

The twelfth scenario parses the canonical closed manifest row descriptor,
labels it structural rather than trusted, rejects a duplicate admission-record
hash, a noncanonical host line, and noncanonical identity base64, and preserves
a canonical BLOCKED reason and resume command.
The shell collector contract statically checks that the emitted Linux/x86_64
live-policy record has the same compiler-free schema and that the production
owner performs no-follow/beneath-root resolution, exact-byte SHA-256 checking,
and same-byte structural parsing before row construction. It also checks the
root-to-boolean internal release gate and ensures the package exports neither a
mutable trusted result nor the raw structural evaluator. The collector fixture
behaviorally compares every emitted Linux/x86_64 manifest field—including all
decoded identities—to its hashed admission record. Behavioral negatives for
symlink swap, path escape, and byte-hash mismatch require a current Simple
runtime; they remain explicit execution **HOLD**, not source PASS. The
executable Simple spec and byte-verifying importer bridge have not been run with
a current self-hosted compiler in this repair session, so typed runtime
admission remains **HOLD** rather than PASS.
