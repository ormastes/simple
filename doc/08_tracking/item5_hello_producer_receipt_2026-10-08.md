# Prospective item5 Hello producer receipt

`check-stage2-hello-world-native-build.shs` can now emit a machine-readable
receipt during a new gate invocation. Plain gate success and historical logs
cannot be imported into this mode. The bridge is optional; existing callers
retain their build/execute and positional no-crash contracts.

Set these environment inputs before invoking the gate with exactly one
`--candidate`:

- `HW_RECEIPT_JSON`: fresh absolute output JSON path; never overwritten.
- `HW_PRODUCER_IDENTITY_JSON`: the coordinated producer's identity record.
- `HW_PRODUCER_SOURCE_ROOT`: its clean Git checkout.
- `HW_RUNTIME_ARCHIVE`: absolute canonical `libsimple_native_all.a` or
  `simple_native_all.lib` path.
- `HW_BACKEND`: requested Hello output backend, `llvm` or `cranelift`.
- `HW_TARGET`: requested target triple; receipt mode currently supports only
  `x86_64-unknown-linux-gnu` and rejects other targets.
- `HW_ARTIFACT_DIR`: existing absolute directory for retained evidence.
- `HW_ROOT`: the checkout containing the Hello fixture, as before.

The identity schema is `item5-phase2-producer-identity-v1`, with required
`compiler_sha256`, `source_commit`, `source_tree_oid`,
`runtime_archive_sha256`, `backend`, and `target`. Optional
`producer_backend` identifies the compiler's own build backend and is distinct
from the requested Hello backend. Unknown/duplicate fields are rejected.
The producer identity must originate from the actual successful coordinated
build's pinned records. This bridge verifies its bindings; it does not infer
how arbitrary binaries were built or provide cryptographic attestation.

Before and after the gate, the bridge checks compiler/runtime hashes,
identity-file hash, clean producer HEAD/tree, fixture hash, and gate/helper
hashes. Runtime selection explicitly uses the archive's parent directory in
both CLI arguments and `SIMPLE_RUNTIME_PATH`, matching the native-all linker
owner's directory contract. The receipt binds that requested runtime authority;
it is not a transitive digest of every object ultimately linked into Hello.
The helper is located relative to the invoked gate script, so a newer bridge
can run against an unchanged frozen producer checkout via `HW_ROOT`.

The gate records NUL-delimited command argv, direct build/run exit statuses,
stdout/stderr, and retained build logs. The entry binary must build and execute
successfully with exactly `hello` or `hello\n`. Receipt mode requires a
little-endian Linux ELF64 ET_EXEC/ET_DYN image for machine 62, and its pre/post-execution hashes
must agree. The positional arm is separately recorded as no-crash/no-timeout;
a clean nonzero positional build remains admissible and is not called an
execution success. Only after these checks does atomic no-overwrite publication
create `item5-phase2-hello-v1` with the fields the existing app manifest v2
validator consumes: `status`, `gate_exit_status`, `compiler_sha256`, and
`source_commit`, plus the bound evidence above. Interrupted/failed attempts
retain diagnostics without a successful receipt.

## Verification scope

`scripts/check/test-item5-hello-receipt.py` uses test-only fake commands and
temporary Git sources. The first six protocol tests passed, including one
actual canonical-gate invocation against a fake compiler; this is not a
Simple/native qualification claim. After correcting runtime-directory command
binding, its focused integration test passed, with retained output at
`build/review/item5-hello-json-bridge-20261008/runtime-directory-command-test.log`.
Final focused verification passed five tests in 13.470 seconds, covering the
real-host-ELF protocol integration, executable mutation, bounded identity
reads, script/wrong-architecture/unsupported-target rejection, and failed or
incomplete execution through the new format check. The tiny ELF payload was
built with host C solely for the protocol test; no Simple compiler was executed.
Logs and source hashes are retained under
`build/review/item5-hello-json-bridge-20261008/` (`final-focused-tests.log` and
`final-inputs.sha256`). Unchanged identity/source negative tests retain their
first PASS and were not replayed. No historical producer was admitted, and actual app
qualification still requires a new successful gate receipt and app execution.
