# SimpleOS Authenticated Loader Hardening — 2026-08-21

Scope: non-bootstrap filesystem executable admission and the scheduler-owned
adoption seam.

The loader keeps path-only and byte-only launch fail-closed. Execution requires
an opaque `ExecutableAuthorityTokenV1`; token minting remains package-private,
and the scheduler is the sole owner that may consume the token, construct the
address space, publish the task, and return an authorization receipt.

This hardening pass closes two artifact-coherence gaps:

- A reread ELF process image must match every attested load-range file offset,
  as well as its address, sizes, and permissions.
- Explicit SimpleOS SMF admission now validates the complete embedded ELF for
  the declared architecture. Matching magic, class, and machine bytes alone do
  not admit an executable.

The ELF artifact gate also rejects unknown permission bits, writable-executable
segments, invalid power-of-two/congruence alignment, overflowing ranges, and
overlapping load ranges before scheduler mapping.

Rollback remains scheduler-owned before publication. Source-close failure after
publication produces `AdoptedCloseRetryable`; the runnable task is retained and
the exact registry token is required for a bounded close retry. No raw handle,
path, blob, or status marker can recreate authority.

Focused coverage:

- `test/01_unit/os/kernel/loader/spawn_pipeline_spec.spl`
- `test/01_unit/os/kernel/loader/smf_loader_hardening_spec.spl`

Verification used the existing self-hosted Linux runtime from the clean main
worktree (SHA-256
`04a38e21d6fbd86149d46d3ee2d761349f8ad29b02c5037a8eb589b6a1b9e4e0`).
Both focused interpreter specs passed. The local deployment wrapper refused its
bounded identity probe; no Rust seed or compiler bootstrap fallback was used.
