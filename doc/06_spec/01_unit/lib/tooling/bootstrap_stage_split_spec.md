# Stage 4 tools-only contract unit specification

> Preparatory contract coverage for the selected bootstrap stage split. Live
> migration admission remains blocked until the legacy pipeline records one
> admitted end-to-end success.

| Tests | Active | Skipped | Pending |
|---|---:|---:|---:|
| 4 | 4 | 0 | 0 |

Source: `test/01_unit/lib/tooling/bootstrap_stage_split_spec.spl`

## Scenarios

### Should accept the canonical Stage 3 authority

Validate a typed compiler manifest, a zero-compiler-source tool journal, and a
linked-tool receipt against the same hashes, target, and ABI identities.

### Should reject compiler traversal and duplicates

Reject compiler-owned source paths, duplicate source/object rows, and every
nonzero compiler-source counter.

### Should reject foreign producer authority

Reject a Rust-seed identity and a journal that is not bound to the canonical
Stage 3 manifest hash.

### Should require executable smokes

Reject a link receipt unless both the built tool's help and version probes pass.

This manual is hand-maintained while the production SPipe/docgen runner is
gated; regenerate it from the executable SSpec after admitted deployment.
