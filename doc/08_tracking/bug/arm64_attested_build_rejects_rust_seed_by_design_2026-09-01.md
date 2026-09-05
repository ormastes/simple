# arm64 attested build: `compiler-version-invalid` is a BY-DESIGN Rust-seed refusal, not a stale binary (2026-09-01)

Status: **OPEN**. Corrects the working hypothesis that a fresh `cargo build
--release --bin simple` would clear the attested build's compiler admission.

## Finding 1 — the fresh seed DOES fix the parser gap (hypothesis confirmed)

Fresh seed built from `origin/main` + PR #273's three commits
(`CARGO_TARGET_DIR=/mnt/data/cargo-target-goal2arm64`, rc=0).
`--version` first line: `Simple Language v1.0.0-rc.1` (deployed 2026-08-26 seed
says `v1.0.0-RC`).

Parse probes, exit code captured directly into a variable, never through a pipe:

| file | rc | first error |
|---|---|---|
| `src/lib/common/encoding/utf8.spl` | 1 | `semantic: cannot compile to standalone SMF: 4 function(s) require the interpreter` |
| `src/os/userlib/fs.spl` | 1 | `semantic: Undefined("undefined identifier: container_view_create")` |
| `src/os/apps/dbd/dbd.spl` | 1 | `semantic: Undefined("undefined identifier: base64_encode")` |

All three are **semantic** diagnostics from standalone single-file compilation.
None is the parser failure recorded in
`arm64_desktop_engine2d_media_chain_blockers_2026-09-01.md` §4
(`fs.spl:537 expected expression, found Dedent`;
`dbd.spl expected expression, found Newline`). The stale-parser blocker is
therefore **cleared by the fresh seed**, and no source was reformatted.

## Finding 2 — the attested builder can NEVER admit any Rust seed

`scripts/check/build-simpleos-arm64-desktop-engine2d-attested.shs` ->
`arm64_guest_validate_native_compiler` /
`arm64_guest_validate_compiler_version_output`
(`scripts/check/lib/simpleos-arm64-guest-source-fingerprint.shs:31,94`) reject a
candidate on two independent axes, before any source is read:

- path filter: `*/compiler_rust/*`, `*/target/debug/*`, `*/debug/simple` ->
  `rust-seed-or-debug-forbidden`;
- version filter: output must be **exactly one line** matching
  `^(Simple v|simple-bootstrap )[0-9]+\.[0-9]+\.[0-9]+...$` and must NOT match
  `Rust-built|bootstrap seed only|debug build` -> otherwise
  `compiler-version-invalid`.

Every Rust seed — the 2026-08-26 deployed one and the fresh one alike — prints

```
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
Simple Language v1.0.0-rc.1
```

three lines, containing both `Rust-built` and `bootstrap seed only`, and whose
version line is `Simple Language v…` not `Simple v…`. It fails the filter on
four separate counts. **`compiler-version-invalid` was the guard working
correctly**, not a stale artifact. Rebuilding the seed cannot change this, and
the guard must not be weakened.

The admissible compiler is a **pure-Simple Stage4 full CLI** — it must also
support `os build --scenario=…`, which the bootstrap CLI
(`src/app/cli/bootstrap_main.spl`, `compile`/`native-build` only) does not.
`scripts/check/admit-simpleos-arm64-server-compiler.shs` ("Admit an undeployed,
provenance-verified Stage4 CLI") is the receipt producer for
`SIMPLEOS_ARM64_ATTESTED_COMPILER` + `SIMPLEOS_ARM64_COMPILER_RECEIPT`.

## Finding 3 — the gate itself is healthy

```
SIMPLE_BIN=<fresh seed> sh scripts/check/check-simpleos-arm64-wm-vulkan-pixel-evidence.shs --selftest
[arm64-wm-vulkan] selftest OK (25 fixtures)
PASS — 25 selftest fixture(s) checked, classifier, fresh-volume anchor, pixel bar and argv guard behave (no boot attempted), renderer=n/a
```
rc=0. (Without `SIMPLE_BIN` it is honestly `ERROR — nothing was checked: no
runnable simple binary for the PPM validator (set SIMPLE_BIN)`, rc=2.)

## Remaining blocker

Produce and admit a pure-Simple Stage4 full CLI. Blocker 2 of
`arm64_wm_vulkan_real_firmware_lane_blocked_2026-09-01.md` — the AAVMF ->
`BOOTAA64.EFI` -> `kernel.elf` `protocol: linux` handover of the arm64 desktop
kernel — remains **UNPROVEN**; no boot was reached.

## Finding 4 — verified against the real builder, and the stage binaries are not the answer

With the **fresh** seed deployed at `bin/release/x86_64-unknown-linux-gnu/simple`,
`sh scripts/check/build-simpleos-arm64-desktop-engine2d-attested.shs` still ends:

```
arm64_desktop_engine2d_attested_build_status=fail
arm64_desktop_engine2d_attested_build_reason=compiler-version-invalid
```
exit 1. Rebuilding the seed changes nothing, as predicted.

A full 3-stage bootstrap was run with the fresh seed (Stage 1 and Stage 2
complete; Stage 3 still linking at the end of this session). Stage 1's artifact:

```
$ bootstrap/stage1/x86_64-unknown-linux-gnu/simple --version
simple-bootstrap 1.0.0-rc.1
$ bootstrap/stage1/x86_64-unknown-linux-gnu/simple os build --help
error: unknown command 'os'
```

So a stage binary **passes** the version filter (`simple-bootstrap X.Y.Z` is an
accepted form) but **cannot run the command the attested builder issues**,
`$COMPILER os build --scenario=arm64-desktop-engine2d` — stage binaries are
`src/app/cli/bootstrap_main.spl`, `compile`/`native-build` only.

The admissible artifact is therefore specifically a **Stage 4 full CLI**
(`src/app/cli/main.spl`, built by `scripts/bootstrap/stage4-tooling-matrix.shs`,
target `cli`), which is exactly the artifact
`scripts/check/admit-simpleos-arm64-server-compiler.shs` exists to admit and
which CLAUDE.md records as not currently deployed anywhere.
