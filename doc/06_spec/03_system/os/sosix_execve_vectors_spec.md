# SOSIX execve vector delivery contracts

Status: authored manual; not generated or executed. `MissingEvidence`: no
admitted pure-Simple test/docgen runtime or live guest receipt.

Executable: [sosix_execve_vectors_spec.spl](../../../../test/03_system/os/sosix_execve_vectors_spec.spl).
Design: [SOSIX execve vectors V1](../../../05_design/os/sosix_execve_vectors_v1.md).
Requirement: REQ-SOSIX-EXECVE-VECTORS-001.

## Host fixtures

1. Prepare `simple build hello.spl` and `SIMPLE_LIB=/lib` in the production
   value planner. Change the caller's second argument to `run`. The retained
   copied bytes must still read `build`, with three argv and one envp entry.
2. Call the production execve owner with empty argv[0], then with a NUL-bearing
   environment value. Both return `-22` before allocating raw memory or making
   a syscall. These cases do not issue a real process replacement.

## Source contracts

1. Inspect SOSIX forwarding into the userlib owner. Both vector tables contain
   addresses inside its raw allocation, and returned syscall status is followed
   by release. No boxed-array `.ptr()` is used as the wire representation.
2. Pin the kernel's 256-byte path, 64/128 table-slot, 4096-byte string and
   32768-byte per-vector limits. Inspect strict UTF-8 conversion after copy-in.

These are source/value checks. They cannot prove physical address validity,
allocation-failure cleanup, guest execution or a compiler running inside
SimpleOS. Physical provider fault tests and live compiler argv/environment
observations remain required by the design.

Run the executable once when an admitted full CLI is available, then run
`simple spipe-docgen test/03_system/os/sosix_execve_vectors_spec.spl --output doc/06_spec --no-index`
and review the generated manual before promoting evidence.
