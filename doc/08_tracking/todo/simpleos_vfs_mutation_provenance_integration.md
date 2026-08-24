# SimpleOS VFS mutation provenance integration

Status: active — phase-1 contracts/owner drafted; runtime integration unverified.

The bounded task/OFD/object mutation-grant owner is only a prerequisite. Do
not describe it as Clang/LLD output proof until all items below are complete:

- derive `TaskExecutionInstanceV1` from the current scheduler task and rotate
  `exec_generation` atomically on exec;
- bind fd aliases to the canonical generational OFD and backend object;
- route FAT32, DBFS, and NVFS create/write/truncate/rename/fsync/final-close
  mutations through the one owner without direct-driver bypasses;
- implement atomic backend compare-and-advance for every retained object and
  namespace epoch; the bounded owner does not retain post-receipt high-watermarks;
- preserve exact backend acknowledgment and indeterminate-outcome retirement;
- assemble a causally ordered receipt set with fsync plus a stable snapshot and
  digest for the same object incarnation;
- add executable SPipe coverage for alias, fork, exec, partial write, rename,
  crash/unknown result, capacity, stale handle, and each filesystem backend;
- compile and execute the filesystem hello-world artifact with admitted
  SimpleOS Clang/LLD only after those gates pass.

No current phase-1 receipt attributes an artifact to a process or toolchain.
