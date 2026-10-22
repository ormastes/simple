# Source-call inventory

`simple gen-lean source-calls FILE.spl TARGET_TRIPLE` produces an unchecked
inventory of resolved direct calls from one self-contained source module.
For example:

```text
simple gen-lean source-calls example.spl x86_64-unknown-linux-gnu
```

The command requires exactly two operands: an existing regular source file
and an explicit target accepted by both the canonical frontend and MIR target
owners. Empty, `host`, and `native` target selections are rejected. It uses the
existing target-aware frontend and its cache contract, checks parser and HIR
diagnostics, and passes the same explicit target context into MIR lowering.
Imports require the unavailable driver module graph. AOP advice and retained
DI bindings require transformations that this route does not perform, so those
inputs are rejected.

A successful command prints the source-text digest, target, frontend cfg
digests, MIR snapshot digest, resolver capture receipt, manifest digest and
binding count. It always prints `formal_status=NOT_CHECKED`. Exit zero means
inventory production completed. Errors return nonzero without an inventory.
The source digest identifies the text read by the existing text-file facade
and supplied to the frontend; it is not a raw-file encoding attestation.

This command does not produce expanded/woven-source provenance or run Lean,
kernel replay, native code, or release admission. It does not change the
existing `generate`, `compare`, `write`, or `verify` modes. The public source
adapter is `compiler.tools.verify.source_calls_v1.source_calls_from_source_v1`.

Source specifications and their pending execution status are documented in
`doc/06_spec/01_unit/compiler/verify/source_calls_v1_spec.md`.
