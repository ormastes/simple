# Compiler-filesystem hex encoding performance evidence — 2026-08-22

Status: **STATIC IMPROVEMENT; NATIVE TIMING BLOCKED**

The guest workflow's private `_cfs_bytes_hex_v2` formatter previously appended
two one-character text fragments for every input byte.  With immutable text,
the copied-prefix proxy is `2n²+n` characters for `n` input bytes.  The revised
Pure-Simple implementation allocates an exact `2n`-byte array, performs exactly
`2n` indexed byte writes, and converts the ASCII byte array to text once.  The
runtime conversion allocates and copies the final `2n`-byte text, so the honest
bound is two linear output-sized allocations rather than one.  Time and peak
live storage are O(n), with no per-byte text fragments. The validator checks
all four stdout/stderr pairs against the adapter's inclusive 65,536-byte cap
before captured-stream hashing or hex allocation; the largest hex result is
therefore 128 KiB and `2n` cannot overflow. Role-file hashes are an earlier,
separate validation phase and are not covered by this capture-stream claim.

Focused coverage in
`test/01_unit/os/port/compiler_filesystem_guest_workflow_v2_spec.spl` checks all
nibble boundaries, lowercase output, exact `2n` output-width scaling at 4 KiB,
the inclusive 65,536-byte boundary, and rejection of 65,537 bytes in every
stdout and stderr slot. The public validator API and accepted wire format are
unchanged; evidence violating the documented capture contract now fails closed.

Native elapsed-time and peak-RSS comparison, the focused SSpec run, and the
Simple optimizer are not reported: this worktree has no admitted executable
`bin/simple`, and the Rust seed/bootstrap is not an allowed substitute.  Run
the same focused spec and optimizer command after the self-hosted runtime is
admitted; until then this document makes no measured runtime-performance claim.
