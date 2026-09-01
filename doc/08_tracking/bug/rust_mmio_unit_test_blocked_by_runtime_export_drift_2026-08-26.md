# Rust MMIO unit test blocked by unrelated runtime export drift

- **Status:** OPEN
- **Filed:** 2026-08-26
- **Area:** Rust seed workspace verification
- **Severity:** high — focused interpreter-provider tests cannot compile

## Evidence

The focused command
`cargo test -p simple-compiler mmio_rejects_null_and_misaligned_addresses_before_volatile_access --lib`
failed before compiling the compiler test target. `simple-runtime` currently
imports symbols that its modules do not export, including
`rt_spin_loop_hint`, multiple TLS configuration/read/certificate functions,
and the `rt_io_udp_*` family. Rust reported four `E0432` groups.

These missing exports are outside the MMIO files and existed before this
tranche. The failure is not evidence against or for the MMIO test; it means the
test did not execute. Do not substitute a different package, disable runtime
features, or call the MMIO Rust change verified.

## Unblock condition

Reconcile the runtime module exports with their implementations and registry,
then rerun the exact focused test once. It must prove null, negative, and
misaligned addresses are rejected before volatile access and an aligned owned
address still round-trips exactly.
