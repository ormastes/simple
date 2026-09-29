<!-- codex-research -->
# Next Beta, Full Bootstrap, and SimpleOS Multiarch — Local Research

Date: 2026-07-30

## Requested outcome

Prepare the next 1.0.0 beta locally, fix release-blocking memory/performance
defects, prove full bootstrap on every supported platform (using GitHub Actions
where the local Linux host cannot), publish SimpleOS x86_64, AArch64, and
RISC-V 64-bit targets, then verify the GitHub release succeeds.

## Current release state

- `VERSION` is `1.0.0-beta`.
- Remote annotated tag `v1.0.0-beta` already resolves to release commit
  `41881d0efb1c`.
- GitHub Actions run `26162779543` for that tag failed. No GitHub Release exists
  for the tag; the latest published release is `v0.9.8`.
- The current checkout is 7,351 commits beyond the beta tag and contains
  extensive unrelated concurrent work. Existing dirty files must not be folded
  into this release lane.

An unchanged version cannot identify a distinct second beta. Reusing or moving
the existing remote tag would make the release non-reproducible. A new
prerelease version and tag are required.

## Existing reusable work

The repository already has a SimpleOS multi-platform research/design chain:

- `doc/01_research/os/simpleos/platform/simpleos_multiplatform_build_local.md`
- `doc/01_research/os/simpleos/platform/simpleos_multiplatform_build.md`
- `doc/02_requirements/os/simpleos/simpleos_multiplatform_build.md`
- `doc/02_requirements/nfr/simpleos_multiplatform_build.md`
- `doc/04_architecture/app/simpleos/simpleos_multiplatform_build.md`
- `doc/05_design/os/simpleos/simpleos_multiplatform_build.md`

It catalogs x86_64/x86_32, ARM64/ARM32, and RV64/RV32. The present release is
narrower: x86_64, AArch64, and RISC-V 64-bit only.

Reusable build/check surfaces include:

- `.github/workflows/rust-bootstrap-multiplatform.yml`
- `.github/workflows/simpleos-build.yml`
- `.github/workflows/release.yml`
- `scripts/bootstrap/bootstrap-from-scratch.sh`
- `scripts/check-simpleos-bootstrap-qemu.shs`
- `scripts/check/check-simpleos-mission-critical-release.shs`
- `scripts/os/simpleos-native-build.shs`
- `scripts/os/simpleos-native-build-aarch64.shs`
- `scripts/os/simpleos-native-build-riscv64.shs`
- `scripts/os/simpleos-sysroot-aarch64.shs`
- `scripts/os/simpleos-sysroot-riscv64.shs`

Canonical target catalog/scenario entries already exist in
`src/os/port/_SimpleosMultiplatformBuild/platform_target_catalog.spl` and
`src/os/_QemuRunner/scenario_catalog.spl`. The missing work is release wiring
and complete target evidence, not another target abstraction.

## Release workflow gaps

1. `.github/workflows/release.yml` packages SimpleOS only as
   `simpleos-${VERSION}-x86_64`.
2. Its SimpleOS job has `continue-on-error: true`; release creation does not
   require SimpleOS success.
3. Bootstrap packaging permits Rust-seed and source-only fallbacks. A green run
   would therefore not prove full self-hosted bootstrap on each target.
4. Release creation does not pass `--prerelease` for a beta.
5. Tag and `VERSION` equality is not enforced.
6. Manual dispatch derives a version from `GITHUB_REF`, which is a branch ref,
   while build artifacts use `VERSION`.
7. SimpleOS packaging tolerates missing expected payloads and can upload an
   incomplete archive.
8. `.github/workflows/simpleos-build.yml` has x86_64-only smoke/full jobs and
   assets. Its full-on-tag condition is ineffective because its trigger does not
   include tags.
9. Release notes describe Linux ARM64/RISC-V and Windows ARM64 as source-only;
   that conflicts with the requested full-bootstrap proof.
10. GHCR uses mutable `latest` even for prereleases.

## Bootstrap and CI state

- The original beta run failed all nine bootstrap matrix entries, SimpleOS,
  full-package creation, and release asset preparation.
- Current main is not release-green: recent runs include FreeBSD seed
  fingerprint, Windows MinGW unresolved `libc`, repo-hygiene, and self-hosted
  stage-3 failures.
- No successful `rust-bootstrap-multiplatform` run was found. Its real native
  full-bootstrap lanes cover Linux x86_64, macOS AArch64/x86_64, and Windows
  x86_64. Linux AArch64/RISC-V64, Windows AArch64, and FreeBSD x86 do not yet
  have equivalent full-bootstrap proof.
- macOS cannot be proven locally; native macOS jobs must remain required GitHub
  Actions gates.
- FreeBSD must use the repository's QEMU/VM or workflow lane rather than treating
  a Linux-host refusal as evidence.

## Memory/performance evidence

- Existing reports
  `doc/09_report/stage4_bootstrap_memory_ceiling_2026-07-25.md` and
  `doc/01_research/compiler/bootstrap/stage4_memory_ownership_research_2026-07-29.md`
  do not prove a green full bootstrap; stage-3/early-OOM work remains open.
- `doc/08_tracking/bug/bootstrap_stage4_selfhost_parse_memory_blowup_2026-07-20.md`
  records an approximately 58 GB stage-4 parse path and incomplete reclamation.
  Existing stage-4 memory check scripts are not wired into GitHub workflows.
- During this research, a broad Simple MCP workspace-symbol query exceeded its
  100 MB watchdog and timed out after emitting a large warning stream
  (`.simple/logs/crash_323126.log`). Do not retry the same broad query. Treat
  this as a tooling performance defect unless an existing owned lane closes it.
- Memory/compiler files are currently dirty in other active lanes. This release
  work must consume their reviewed result or coordinate ownership, not overwrite
  them.

## Minimal implementation direction

Reuse the strict full-bootstrap workflow and existing per-architecture SimpleOS
builders. Add only the missing hard gates and artifact matrix:

1. Enforce tag equals `v$(cat VERSION)` and mark hyphenated versions prerelease.
2. Require full self-hosted bootstrap artifacts for every supported host target;
   remove release fallbacks that manufacture source-only success.
3. Make SimpleOS a required x86_64/AArch64/RISC-V64 build, boot/evidence, and
   package matrix.
4. Fail when any expected per-architecture image, compiler-in-filesystem
   evidence, checksum, or mission-critical gate is absent.
5. Create the release only after whole tests, bootstrap matrix, SimpleOS matrix,
   payload checks, and memory/performance evidence pass.
6. Do not update mutable `latest` for a prerelease.

AArch64 and RISC-V64 currently have kernel/FAT32 and QEMU surfaces but not the
same bootable installer-media contract as x86_64. Release them with accurate
kernel/image labels; do not call them installers until that contract passes.

## Version source drift

The release skill's four-location list is stale. Current metadata searches find
version-bearing fields in `VERSION`, `config/bootstrap.sdn`,
`src/app/cli/bootstrap_identity.spl`, `src/app/cli/cli_helpers.spl`,
`src/app/cli/_CliMain/args_and_os_commands.spl`,
`src/app/simpleos_tool/main.spl`, `src/app/simple.sdn`,
`src/compiler/simple.sdn`, `src/lib/simple.sdn`,
`src/compiler_rust/Cargo.toml`, `src/compiler_rust/Cargo.lock`, and
`src/compiler_rust/simple.sdn`. Implementation must establish which are
canonical/generated, update the release skill/checker, and verify consistency
without blindly replacing unrelated version strings.

## Research review

Parallel read-only lanes covered compiler/bootstrap, SimpleOS sources and CI
packaging, documentation/history, and live GitHub state. The primary Codex pass
reviewed and merged their findings. No lower-model sidecar authored accepted
requirements; final reviewer is the primary/highest-capability Codex model.
