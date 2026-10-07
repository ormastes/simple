# Native file hashing allocates the whole artifact

The Rust owner of `rt_file_hash_sha256` used `std::fs::read` before hashing.
Compiler identity construction hashes the executable and runtime archives;
the retained Phase 2 candidate is 518,828,064 bytes. Hashing it therefore
requires an unnecessary file-sized temporary allocation. The C owner already
streams the input.

The repair reads through a fixed 64 KiB buffer, retries interrupted reads,
and preserves lowercase SHA-256 output and nil on open/read failure. No
resource limit or compiler admission rule changes.

Regressions exercise binary data at both sides of the buffer boundary, empty
input, missing/unreadable inputs, and a sparse 128 MiB zero-filled artifact
with an independently calculated digest. The large fixture allocates no
file-sized input and is intended to run under a 64 MiB RSS cap.

This is a concrete allocation defect, not yet proof of the complete cause of
the historical 5.6 GiB Phase 2 Hello failure. Runtime checks, measured RSS,
and rebuilt-compiler qualification are pending.
