<!-- codex-design -->
# M5 Hermetic Portable Qualification Test Plan

Requirements: `MBH-REQ-007`, `MBH-NFR-004`.

| Evidence | Expected result |
|---|---|
| Clean explicit three-file fixture | PASS with matching source/snapshot inventory digests |
| Undeclared decoy file | Excluded from snapshot |
| Source mutation before execution | FAIL before checker starts |
| Source mutation during execution | Checker may finish from snapshot; wrapper FAILS |
| Snapshot mutation during execution | FAIL regardless of checker exit |
| Driver-source mutation | FAIL while snapshotted driver remains stable |
| Required-file symlink | FAIL before copy |
| Focused M5 portable qualification | Runs only through the proven wrapper |

Native slices, Apple signing/notary, promotion, commit, and deployment are not
part of this portable wrapper test.
