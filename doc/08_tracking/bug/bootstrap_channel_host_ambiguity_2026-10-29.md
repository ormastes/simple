# Pinned Rust channel with multiple installed Windows hosts

Status: resolver regression PASS; real authority fingerprint PASS. The bootstrap
build and runner qualification remain separate gates.

The authority fingerprint reported `settings-host=channel-toolchain-absent`
with `default_toolchain = "stable-x86_64-pc-windows-msvc"` and both
`nightly-2026-09-15-x86_64-pc-windows-msvc` and
`nightly-2026-09-15-x86_64-pc-windows-gnullvm` installed. The pinned channel
existed; its unqualified directory scan rejected two host candidates.

The resolver now retains the fully qualified default toolchain when its channel
differs, and restricts installed pinned-channel candidates to its exact host
suffix. It does not use ambient `RUSTUP_TOOLCHAIN`: execution pins its own
channel, so an unrelated ambient override must not alter the fingerprint.
Existing duplicate/malformed settings rejection is unchanged. A missing chosen
host and multiple matching directories still fail closed; no host is guessed.

`scripts/check/check-bootstrap-channel-host-selection.shs` passed using MSYS
bash with its Unix tools on PATH and `MSYS=winsymlinks:nativestrict`. It covers
unique/ambiguous candidates, selected MSVC/GNU hosts, dated default channels,
missing or malformed host selectors and symlink exclusion.
The complete installed-toolchain resolver also passed mismatched settings with
both Windows hosts, plus duplicate/malformed settings rejection, using fixture
compiler metadata instead of executing a compiler.
Initial Windows
test setup without strict native symlinks copied the fixture instead of making
a symlink; that setup failure is not a provider regression. This shell test
does not establish a completed bootstrap or passing test runner.
