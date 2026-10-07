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

## Verification

The three runtime tests passed (zero failures/ignored, 1,371 unrelated tests
filtered) under an enforcing 65,536 KiB process-tree cap. Peak RSS was 8,312
KiB. The large-file case verified the fixed digest
`254bcc3fc4f27172636df4bf32de9f107f620d559b20d760197e452b97453917`.

An identical C probe called the actual public ABI in the historical and fresh
native-all archives. Both produced that digest and exited zero. Kernel
`getrusage` peak RSS fell from 135,016 KiB to 8,232 KiB, about 93.9 percent.
The candidate also passed the 64 MiB cap. These are isolated file-hashing
measurements; the historical archive differs in other source revisions, so
this is not a controlled whole-runtime performance comparison.

Evidence: `/var/tmp/compiler-streaming-sha256-20261007/`, including the
`public/` probe logs and watchdog receipts. Candidate source SHA-256:
`ca4930ade3215343ba98dfa3f238b43d866f403a2341b6b00c354a3a69cc553b`.
Fresh native-all archive SHA-256:
`6ca86625f7e19bf72eb7c086ca96e3138fbcca71a612d620630ded6bca8ed5b8`.

The native-all build passed at 3,766,568 KiB peak under the normal 5,859,375
KiB limit after an earlier temporary 3 GiB concurrent-build reservation was
insufficient. The failed receipt and compatible cache were preserved. All 14
local gates, environment guards, whitespace and documentation-layout checks
passed for the source repair.

This fixes a concrete allocation defect. It does not yet prove the complete
cause of the historical 5.6 GiB Phase 2 Hello failure; rebuilt-compiler and
full-bootstrap qualification remain separate pending criteria.
