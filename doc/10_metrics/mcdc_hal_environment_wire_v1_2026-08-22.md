# MC/DC HAL environment wire V1 performance evidence

- Revision under test: working copy before lane commit, 2026-08-22 UTC.
- Command: `cc -O3 -std=c11 -D_POSIX_C_SOURCE=200809L
  src/runtime/test/environment_instruction_wire_v1_selfcheck.c` followed by the
  resulting selfcheck under `/usr/bin/time`.
- Workload: 10,000,000 exact one-record frames, including header and record
  validation on every iteration.
- Result: 24.81 ns/record; process peak RSS 1,536 KiB (`getrusage` observed
  1,024 KiB before process teardown accounting).
- Allocation model: fixed 128-byte caller/stack frame and scalar cursor; the
  decoder contains no allocation, slicing, text conversion, map, or hashing.
- Complexity: O(1) per 96-byte record and O(N) for an N-record frame. Header
  admission is O(1). Exact frame length prevents trailing-data scans.
- Simple optimizer: not run because the deployed Pure Simple compiler is not
  currently admissible; the Rust seed was not substituted. This native oracle
  is independent contract/performance evidence, not a replacement
  implementation.
