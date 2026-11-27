# Local authority policy specification

Status: **NOT_RUN**. Authored manual; not generated execution evidence.

Executable: `test/03_system/app/orchestrator/feature/local_authority_policy_spec.spl`.
Implementation: `src/lib/nogc_sync_mut/orchestration/local_authority_policy_v1.spl`.

| Requirement | Authored case | Evidence asserted |
| --- | --- | --- |
| HOST-LOCAL-POLICY-01 | Decodes canonical public metadata through the existing authority validator | Snapshot generation, session generation, exact source digest and decoded public key bytes |
| HOST-LOCAL-POLICY-01 | Rejects malformed/noncanonical source and unrecognized fields | Parser rejection, canonical spelling, unknown continuity field and private-key exclusion |
| HOST-LOCAL-POLICY-01 | Rejects invalid roles, encodings, duplicate identities and policy mismatch | Existing authority validator errors; public-key length/hex bounds; UTF-8 source byte bound (including 300000 four-byte characters); positive typed session generation |
| HOST-LOCAL-POLICY-02 | Checks protected filesystem root and pinned bytes before decoding | Actual secure temporary directory and policy file; digest mismatch/tampering; private modes; absolute UTF-8 byte-bounded root (including multibyte input); traversal/control characters; bounded external pin |

| HOST-LOCAL-POLICY-02 | Refuses actual symlink roots and policy leaves | Owned package symlink facade creates real links inside a secure temporary tree; rejects root/leaf links, checks target bytes, unlinks links before tree cleanup |

The local administrator provisions public verification policy. The caller must own a root created with `secure_temp_dir` and retain a trusted ancestor tree. A digest and mode bits do not authenticate an arbitrary root. No UID getter is available, and this code does not claim race-free descriptor-relative IO, enrollment, host boot/provider continuity, or runtime authorization merely from loading policy.

Missing evidence: compilation and SSpec execution have not run. Actual root and policy-leaf symlink rejection tests are authored using `std.nogc_sync_mut.package_sffi.create_symlink`; these cases remain NOT_RUN. No race-resistance or live runtime qualification is claimed.
