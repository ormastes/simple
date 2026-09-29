<!-- codex-research -->
# Next Beta, Full Bootstrap, and SimpleOS Multiarch Requirements

Date: 2026-07-30
Selection: user selected Feature Option A on 2026-07-30.
Version: `1.0.0-beta2`
Tag: `v1.0.0-beta2`

## Scope

Produce a distinct, reproducible GitHub prerelease only after the repository,
host bootstrap matrix, and SimpleOS x86_64/AArch64/RISC-V64 release targets pass
their real acceptance gates. Existing target catalogs, bootstrap entrypoints,
and evidence checkers are reused; this feature does not create a second target
model or release framework.

## Requirements

### REQ-001 — Immutable beta2 identity

All canonical version sources SHALL resolve to `1.0.0-beta2`. A tag-triggered
release SHALL fail unless the tag is exactly `v1.0.0-beta2` and matches
`VERSION`. GitHub SHALL publish it as a prerelease. The existing
`v1.0.0-beta` tag SHALL not move or be reused.

### REQ-002 — Fail-closed full bootstrap matrix

Every advertised host package SHALL be produced by the repository's canonical
full self-hosted bootstrap route and SHALL contain a verified non-Rust-seed
Simple runtime. Linux, Windows, macOS, and FreeBSD lanes SHALL be required.
Architecture rows advertised as executable packages SHALL pass their native or
emulated execution gate. Rust-seed fallback, committed stale binary fallback,
source-only success, `continue-on-error`, and missing-runtime packaging SHALL
fail the release.

macOS proof MAY run only on native GitHub-hosted macOS runners because the local
Linux host cannot supply native macOS evidence. This is a location exception,
not a release-gate exception.

### REQ-003 — Three SimpleOS release targets

The release SHALL contain distinct x86_64, AArch64, and RISC-V64 SimpleOS
packages generated through the existing platform target/scenario catalogs.
Each architecture SHALL provide:

1. a nonempty kernel/native payload;
2. its architecture-appropriate bootable disk/FAT32/image artifact;
3. a successful bounded QEMU boot/runtime transcript;
4. a target-native Simple compiler payload embedded in the filesystem;
5. in-guest `simple --version` and compile/run `hello world` evidence;
6. SHA-256 checksums and retained provenance.

AArch64/RISC-V64 artifacts SHALL be labeled as kernel/images, not installers,
until their installer-media contract matches x86_64.

### REQ-004 — Memory and performance release gates

Full bootstrap, whole tests, packaging, and SimpleOS jobs SHALL record wall
time and peak RSS and SHALL not OOM or time out. The release SHALL run the
existing stage-4 memory gates and fix release-path defects they expose.
After the first trustworthy green baseline is retained, a greater than 10%
wall-time or peak-RSS regression on the same runner class SHALL fail. The first
green beta2 run establishes that baseline while remaining bounded by explicit
job timeouts and runner memory.

### REQ-005 — Verified GitHub publication

Release creation SHALL require successful whole tests, verification, every
bootstrap row, every SimpleOS row, the SimpleOS mission-critical gate with
`release_blockers=none`, artifact inventory validation, and checksum
validation. A prerelease SHALL not update mutable `latest`.

After push, the release owner SHALL inspect the actual GitHub Actions run and
GitHub Release, fix any failure, and repeat within the bounded three-cycle
limit. Completion requires a successful workflow, `prerelease=true`, exact tag
and version, and the complete expected asset inventory.

## Exclusions

- Moving or deleting `v1.0.0-beta`.
- Claiming physical-board evidence from QEMU.
- Calling AArch64/RISC-V64 images installers before their installer contract
  passes.
- Shipping source-only packages as full-bootstrap evidence.
- Publishing, pushing, or retagging before verification PASS and explicit user
  approval to push.
