# Bootstrap fingerprint rejects rustup host with ambiguous pinned-channel toolchains (2026-10-22)

## Symptom

`bootstrap-from-scratch.sh` aborts in `phase=fingerprint` with
`rust-toolchain-check=settings-host=channel-toolchain-absent` (see
`.simple/storage/build/bootstrap/rust-authority-fingerprint-error.log`).

## Root cause

`src/compiler_rust/rust-toolchain.toml` pins `channel = "nightly"`. The
bootstrap's fail-closed toolchain resolver
(`bootstrap_stage3_resolve_rust_toolchain` in
`scripts/check/lib/bootstrap-stage3/authority.shs`) reads rustup's
`settings.toml` `default_toolchain`:

- If the default names the pinned channel, it is used directly
  (`settings-host=pass`).
- Otherwise the resolver scans `~/.rustup/toolchains/` for `nightly-*`
  directories and requires EXACTLY ONE non-symlink match
  (`bootstrap_stage3_channel_toolchain_host`, lines ~1332-1352): "zero or
  several (e.g. a dated nightly alongside a plain one) is ambiguous and fails
  closed."

This host had `default_toolchain = "stable-x86_64-pc-windows-msvc"` AND two
non-symlink nightly toolchains installed
(`nightly-x86_64-pc-windows-msvc` and
`nightly-2026-09-15-x86_64-pc-windows-msvc`), so the scan counted 2 and
failed closed.

## Fix (host state, reversible)

`rustup default nightly` — the settings path then names the pinned channel
directly and the ambiguous scan is never needed. The dated nightly remains
installed and usable; undo with `rustup default stable` if a different global
default is required.

## Evidence

- Reproduced 2026-10-22 on `release_phase3`: fingerprint log ends at
  `settings-host=channel-toolchain-absent`.
- After `rustup default nightly`, the resolver proceeds
  (`settings-host=pass`) and the bootstrap enters Stage 1/2 work.
