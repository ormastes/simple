# Cargo Feature-Gate Dependency Map (SimpleOS fork)

SimpleOS has no `fork` / `exec` / sockets, so any Cargo code path that
tries to reach the network or spawn a helper must be compiled out when
`target_os = "simpleos"`. This doc lists the upstream files that need
`#[cfg(not(target_os = "simpleos"))]` guards in the `ormastes/rust`
fork. No patches are committed here; this is the dependency map used
when authoring those patches.

## Network I/O (must gate)

- `src/tools/cargo/src/cargo/sources/registry/remote.rs`
  HTTP access to crates.io index. Gate entire module.
- `src/tools/cargo/src/cargo/sources/registry/http_remote.rs`
  Sparse-index HTTP backend. Gate entire module.
- `src/tools/cargo/src/cargo/sources/git/utils.rs`
  libgit2 network fetches. Gate fetch helpers.
- `src/tools/cargo/src/cargo/sources/git/source.rs`
  Git source provider. Gate update/fetch paths.
- `src/tools/cargo/src/cargo/ops/cargo_fetch.rs`
  Top-level `cargo fetch` entry. Gate the whole op; force offline.

## Subprocess spawn (must gate)

- `src/tools/cargo/src/cargo/util/command_prelude.rs`
  `exec()` helpers. Gate anything that spawns a long-running helper.
- `src/tools/cargo/src/cargo/ops/cargo_install.rs`
  Invokes `cargo build` recursively; gate or redirect to in-process.
- `src/tools/cargo/src/cargo/util/network/retry.rs`
  Retries on network errors; gate to always return Ok(()) (no-op).

## Registry auth (must gate)

- `src/tools/cargo/src/cargo/util/auth/mod.rs`
  Credential provider spawn. Gate to a stub that returns
  `Err(Offline)`.
- `src/tools/cargo/src/cargo/ops/registry/publish.rs`
  `cargo publish`. Gate entirely; publishing is host-only.

## Expected behaviour after gating

- `cargo build --offline` works using only `./vendor/`.
- `cargo fetch`, `cargo publish`, `cargo search` fail fast with a
  clear "not supported on SimpleOS" error.
- `cargo vendor` remains usable on the host Linux build only.
