# Planner admission required GNU sha256sum on macOS

**Priority:** P1

**Status:** Fixed with a focused shell regression; no full bootstrap run.

The planner admission v2 producer and shared receipt verifier called
`sha256sum` directly for file hashes, runtime snapshots, text hashes, and the
cache scope key. The native macOS PATH provides `shasum`, so admission could
fail before building the planner. Pipelines ending in `awk` could also hide
the checksum command's failure and return an empty successful result.

The shared helper now selects GNU `sha256sum` or macOS `shasum -a 256` while
preserving the checksum record format. Digest extraction checks the checksum
command status and validates a 64-character lowercase hexadecimal digest.
Producer snapshots use the same provider and refuse a hashing failure.

Regression: `sh test/00_unit/scripts/bootstrap_planner_portable_hash_spec.shs`.
The fixture supplies only `shasum` on PATH, checks known file/text/stream
digests and exact multi-file snapshot records, and rejects missing files,
missing providers, and a provider that emits a valid digest but exits nonzero.

Validation: the focused regression passed on macOS. The existing producer and
verifier gate also passed all 13 fixtures under `PATH=/usr/bin:/bin`, exercising
the complete admission flow with native macOS tools and fixture compilers.

Executable SSpec: `test/02_integration/compiler/bootstrap_planner_portable_hash_spec.spl`.
It executes the isolated shell regression through the process facade and adds
direct production-helper scenarios for a failed provider and empty input.
SSpec execution and SPipe docgen are pending a qualified full CLI. The binary
at `bin/release/aarch64-apple-darwin/simple` was identified as a Rust bootstrap
seed; its attempted invocation is excluded from verification evidence. The
direct shell commands used by the added scenarios were checked independently.
