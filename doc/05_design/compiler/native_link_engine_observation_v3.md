# Completed native link engine observations

`NativeLinkSuccessV1` is the existing execution owner's result. Its engine ID
describes the branch that actually completed, including external `cc` fallback.
The LLVM orchestrator now carries that result into the optional
`NativeLinkedArtifactV2.actual_engine_id`; path-only APIs keep returning paths.
Retained cache hits and unsupported legacy routes have no current observation.

SimpleOS user links cover the shared aarch64/riscv64/i686/arm32/riscv32 path and
the separate x86_64 userspace path. The internal facade reports the established
`internal:simpleos` ID only after the in-house BootLayoutPlan/ELF implementation
publishes successfully; this implementation has no external fallback. The
external user branch reports `ld.lld` only after the invoked linker succeeds.
Legacy kernel link results do not acquire userspace engine observations.

The already cache-ineligible SimpleOS driver path may publish a version-three
observation at the existing `<output>.link-receipt` location after a successful
link, stable SDK inputs across the link, and a final output digest. It binds the
exact engine, canonical target and architecture, output SHA-256, and a checksum
of the canonical receipt body. Publication failure returns an error. Version
three explicitly records completed, fresh-only and cache-authority-none facts;
existing version-one/two cache readers do not accept it for reuse.

The matrix removes old output and receipt before each invocation and refuses
to run the row if removal failed. After successful compilation it compares the
entire canonical observation against the current output bytes, expected target,
and exact engine allowlist (`internal:simpleos` or `ld.lld`). Missing, malformed,
wrong-target, changed-output, unknown-engine and fallback-mismatch observations
are `UNVERIFIED` and cannot count as passing rows. ELF/PE checks and actual guest
tool execution remain separate requirements.

The physical shell fixtures verify the observation reader and its rejection
paths, not actual linker or guest execution. The Simple codec cases are authored
but require a rebuilt pure-Simple producer. All requested real matrix executions
remain unverified until their own outputs and receipts are retained.
