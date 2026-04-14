# Vendored Crates for the Rust Seed Compiler

This directory holds a mirror of every crate referenced by
`src/compiler_rust/Cargo.lock`. The contents are populated by
`cargo vendor` and MUST be committed to the repository so that SimpleOS
self-builds (which have no fork/exec and therefore no way to call
`git` or `curl`) can compile fully offline.

## Refresh procedure (run on a host with network)

```sh
cd src/compiler_rust
cargo vendor --respect-source-config > .cargo/config.toml.fragment
```

Then merge any new entries from `.cargo/config.toml.fragment` into the
existing `[source.*]` blocks in `.cargo/config.toml` (do NOT overwrite
the file - it also carries linker and target settings). Delete the
fragment once merged, then `jj commit` the updated `vendor/` tree.

## Caveats

- First run requires network access. After that all builds must use
  `cargo build --offline`.
- Do not `.gitignore` anything under `vendor/`; checksums are part of
  the lock contract.
- Keep `.gitkeep` so the directory survives even when empty.
