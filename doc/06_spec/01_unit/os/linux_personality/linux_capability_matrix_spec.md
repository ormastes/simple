# Linux capability matrix spec

Source: `test/01_unit/os/linux_personality/linux_capability_matrix_spec.spl`

The Linux-personality capability matrix is an admission boundary. Overlapping
ABI and syscall rows are adapted from `LinuxPersonalityContract`, the sole
status owner. A capability is not `ready` unless its corresponding contract is
implemented. The current futex syscall remains an explicit `stub`, so it cannot
satisfy readiness or game admission.

The game-profile admission gate independently requires a fully implemented
futex. Mmap, clone, and signal may be degraded only where their documented
partial modes remain usable.

`evaluate_from_posix()` is idempotent: it rebuilds its bounded syscall snapshot
instead of appending duplicate rows on repeated health checks.

The executable spec constructs the matrix and asserts the futex row and ready
count.  A passing run with the deployed bootstrap seed is diagnostic only; a
fresh provenance-admitted pure-Simple tool is required for release evidence.
