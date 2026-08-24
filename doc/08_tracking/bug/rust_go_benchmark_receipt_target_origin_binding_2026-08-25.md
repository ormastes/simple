# Rust/Go benchmark receipt target and origin binding gap

Status: OPEN. The `rust-go-benchmark-parity` ledger row remains TODO.

The lane-specific numeric oracle now validates a Linux ELF executable/shared-
object header, binds class/endianness/machine to the declared environment,
requires distinct Simple/Rust/Go blobs, recomputes all retained statistics,
and verifies the canonical live Stage 4 compiler chain. This closes fabricated
or mismatched executable-header evidence but does not complete artifact origin.

Two bindings remain before an external receipt may promote the row:

1. `simple.must-check-target/v1` still accepts generic `target_kind` and
   `target_id` tokens. The external importer must require a benchmark-host
   identity and cross-bind it to the environment OS/architecture consumed by
   the lane-specific oracle.
2. Distinct hashes do not prove that the three blobs were produced from the
   committed Simple/Rust/Go sources. Closed build receipts must bind each
   source hash, compiler/toolchain hash, compile flags, output hash, and exit
   status. The validator must recompute those bindings rather than trusting a
   signed language label.

Required mutations: target/environment architecture disagreement, target/ELF
machine disagreement, substituted output with updated hash, wrong source hash,
wrong toolchain hash, and compile-command/output contradiction. Until those
fail closed and real benchmark samples pass under an independently reviewed
receipt, no TODO-to-PASS promotion is authoritative.
