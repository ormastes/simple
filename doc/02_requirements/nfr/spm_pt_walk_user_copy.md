# SPM pt-walk user-copy NFR

Feature: FR-SPM-0001.

- NFR-SPM-0001-001: Copy validation must walk at page granularity, not byte by
  byte, before the actual byte copy.
- NFR-SPM-0001-002: The hot syscall path must avoid new heap allocations except
  for the returned kernel-owned byte buffer.
- NFR-SPM-0001-003: Tests must cover nil translation, execute-only VMA rejection,
  cross-page tail rejection, and EFAULT copy-in behavior.
