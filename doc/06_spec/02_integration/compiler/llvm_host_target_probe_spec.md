# LLVM host target probe integration spec

Executable source:
`test/02_integration/compiler/llvm_host_target_probe_spec.spl`.

The spec calls the compiler's LLVM host architecture and OS probes. It
requires nonempty results on every host. On Linux it requires the architecture
to equal the standard runtime's host architecture and the OS to be `linux`.
This catches a broken import migration or changed Linux target mapping while
allowing the existing fallback behavior on other hosts.

The 2026-09-28 focused native before/after executions each reported one
example and zero failures. See
`doc/09_report/compiler/target5_llvm_host_probe_closure_2026-09-28.md` for
binary identities and the scope of the measurement.
