# SCV storage failure contracts

Source: `test/01_unit/lib/scv/storage_failure_spec.spl`.
Requirements: `REQ-SCVN-B03-READ`, `REQ-SCVN-B03-PUBLISH`.
Status: authored manual; execution, generated-manual review and maintenance
scan **not_run** without a qualified native runtime.

The ten authored scenarios cover empty-file SHA-256 versus absent/directory
input; failed-buffer rejection without an empty chunk; invalid/excess/exact
bounds; read-once binary capture after source replacement; text staging failure
without non-atomic fallback; byte-exact binary atomic publication and failure;
failed chunk staging; failed rename preserving its destination directory;
explicit symlink refusal; and corrupt existing-chunk rejection.

The empty and `abc` digests are literal standard SHA-256 values. Binary arrays,
retained text and directory markers are read from real files after exercising
the implementation. These oracles do not recompute their expected result using
the storage helper being tested. Staging-directory faults need no root-sensitive
permission assumptions. Sync failure, an actual concurrent grow race, directory
fsync and power-loss recovery require additional executed evidence.
