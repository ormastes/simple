# Execve wire-plan unit specification

Status: authored, execution and docgen `MissingEvidence`.

Executable: `test/01_unit/os/sosix/execve_plan_v1_spec.spl`.
Requirement: REQ-SOSIX-EXECVE-VECTORS-001.

The cases pin pointer-free packet offsets and terminating zero bytes; preserve
explicit argv[0], UTF-8, empty trailing arguments and environment order; reject
empty paths/argv[0], embedded NUL, malformed UTF-8, oversized paths/strings,
missing NULL table slots and exhausted per-vector byte budgets. Boundary
fixtures admit exactly 63 arguments, 127 environment entries, 256 path bytes,
4095 string bytes plus NUL and 32768 aggregate vector bytes.

No test in this file exercises a physical syscall or guest. See
`doc/05_design/os/sosix_execve_vectors_v1.md` for required native/guest evidence.
