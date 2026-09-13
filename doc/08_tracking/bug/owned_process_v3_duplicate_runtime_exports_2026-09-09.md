# OwnedProcess V3 duplicate runtime exports

Date: 2026-09-09  
Status: fixed prerequisite; pending final runtime verification.

The Rust runtime facade previously exported five NIL/false
`rt_process_owned_v3_*` placeholders while `runtime_process_owned.c` exported
the canonical stateful implementations with the same ABI names. Linking the
runtime with its required whole-archive C capsule fails with duplicate symbols
for input, cancel, result, collect, and release.

Registrations and Simple extern declarations remain unchanged. Removing the
Rust placeholders selects the canonical C definitions rather than deleting the
ABI.

## Acceptance

- Restoring any placeholder reproduces the five duplicate-symbol link failure.
- With the placeholders absent, the runtime links against the whole-archive C
  capsule and compiler tests execute.
- Runtime symbol registrations and Simple declarations remain present.
