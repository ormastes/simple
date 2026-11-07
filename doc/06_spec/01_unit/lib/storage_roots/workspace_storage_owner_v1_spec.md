# Workspace storage owner contract

Source: `test/01_unit/lib/storage_roots/workspace_storage_owner_v1_spec.spl`.
Status: five authored SSpec scenarios, **NOT_RUN**. This is a manually reviewed
mirror, not generated docgen output. Native negative evidence is separate at
`workspace_storage_owner_v1_native/evidence.sdn`.

| Scenario / step | Real assertion | Evidence limit |
|---|---|---|
| Validate actual production storage request contracts before native effects | Traversal, missing project, unsupported kind and non-512-byte Linux limit reject; valid contract accepted | Contract acceptance does not admit a filesystem |
| Decode a native-shaped observation through the real owner decoder | Exact pool/workspace/quota/hard bytes/policy correlate; measured usage preserved; changed immutable request changes digest | Supplied record exercises parser, not native quota |
| Keep dirty or partially cleaned storage charged | Released Linux projection rejects nonzero blocks or inodes | Zero-shaped projection is not cleanup authority |
| Refuse uncorrelated or malformed provider data | Empty, extra, unknown-state, noncanonical and oversized numeric records reject | Native failure separately returns no receipt |
| Distinguish a native volume bound from an inode or cleanup capability | Windows requires unknown inode usage `-1`; zero and released projections reject | No Windows execution or disposal claim |

The native selfcheck uses the actual hosted Core-C runtime and real temporary
directories. One Linux run passed 73 dynamic checks: unsupported/mismatched scope
refusal, traversal/symlink rejection, stale token refusal, dirty-file and mode
preservation, and equal descriptor counts after 40 refused admissions. It never
injects a successful quota result, runs privileged setup, or treats missing
platform facilities as a passing positive test.

Pending mandatory verification: admitted Simple compiler and real runner/docgen;
administrator-provisioned XFS enforcement with independent quota readback and a
write reaching EDQUOT; quota-disable/identity replacement refusal; retained dirty
cleanup and restart recovery; configured Windows NTFS volume identity/length and
over-capacity behavior; independent Windows disposal authority and lifecycle;
same-host-journal reserve/release integration. All remain **NOT_RUN/BLOCKED**.

Initial Windows release is explicitly unsupported and retains handles/charge.
Linux recovery after a process restart with an already-absent workspace remains
pending. Neither a decoded receipt nor process exit authorizes deletion or host
capacity discharge. These limitations are required follow-up implementation,
not acceptance exclusions.
