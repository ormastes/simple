<!-- codex-architecture -->
<!-- codex-design -->
# Next Beta Full Bootstrap and SimpleOS Multiarch Architecture

Status: Accepted by user selection of Feature A + NFR A on 2026-07-30.

## Context

The existing `v1.0.0-beta` tag is immutable release history but its GitHub
Actions run failed and no GitHub Release exists. The current release workflow
can package Rust-seed/stale/source-only fallbacks, treats SimpleOS failure as
non-blocking, and emits only an x86_64 SimpleOS package. Existing compiler,
platform, QEMU, payload, and mission-critical owners already express nearly all
needed behavior.

## Decision

Use `.github/workflows/release.yml` as the single release coordinator and
harden its current jobs. Do not add a release service, target registry, or
MDSOC capsule.

The workflow is a fail-closed artifact DAG:

```text
check-version
  ├─ build-bootstrap[host/arch/backend]
  ├─ build-freebsd-bootstrap
  ├─ bootstrap-memory
  ├─ whole-tests
  └─ simpleos-build[x86_64|aarch64|riscv64]
             │
             v
    simpleos-mission-critical
             │
             v
      release-preflight
             │
             v
        create-release
             │
             v
        verify-release
```

Every edge carries immutable artifacts or receipts from the exact tag commit.
Release creation consumes those artifacts; it does not rebuild them.

## Existing owners

| Concern | Canonical owner |
|---|---|
| Canonical version | `VERSION` plus validated metadata/version sources |
| Full bootstrap | `scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap` |
| Host matrix | `.github/workflows/rust-bootstrap-multiplatform.yml`, `.github/workflows/windows-build.yml`, `.github/workflows/freebsd-build.yml` |
| SimpleOS target definitions | `src/os/port/_SimpleosMultiplatformBuild/platform_target_catalog.spl` |
| SimpleOS scenarios | `src/os/_QemuRunner/scenario_catalog.spl` |
| x86_64 full evidence | `scripts/check-simpleos-bootstrap-qemu.shs --full` |
| AArch64 build/evidence | `scripts/check/build-simpleos-arm64-desktop-engine2d-attested.shs` and catalog scenario |
| RISC-V64 build/evidence | RISC-V64 catalog scenario and `scripts/qemu/check_simpleos_rv64_serial_shell.shs` |
| Target-native compiler payloads | `scripts/ci/build-simpleos-toolchain.shs --require-all` and existing architecture builders |
| SimpleOS release trust | `scripts/check/check-simpleos-mission-critical-release.shs` |
| Stage-4 memory | `scripts/check/check-stage4-memory-gate.shs`, `check-stage4-selfhost-parse-memory*.shs` |
| Payload safety | `scripts/check_release_payload.shs` |
| GitHub publication | existing `gh release create` workflow step / `src/app/release/github.spl` |

## Release identity boundary

`check-version` owns release identity:

1. read and trim `VERSION`;
2. reject anything except `1.0.0-beta2` for this release;
3. on tag events require `GITHUB_REF_NAME == "v${VERSION}"`;
4. pass the same version output to every package and note generator;
5. derive prerelease status from a hyphenated SemVer suffix;
6. never derive a release version from a branch ref.

All other jobs consume `needs.check-version.outputs.version`. No job parses
`GITHUB_REF` independently.

## Full-bootstrap boundary

An advertised executable package is valid only when its row:

1. runs the canonical full-bootstrap route on a native runner or a named,
   required emulation lane;
2. rejects Rust-seed identity;
3. executes the produced CLI;
4. packages that exact verified artifact;
5. emits a receipt and digest.

Cross-compiling one object, packaging source, or copying a committed binary is
supporting evidence, not a full bootstrap. Unsupported rows must be removed
from release notes rather than reported green.

macOS remains a required native GitHub Actions lane. The local Linux host does
not emulate macOS proof.

## SimpleOS target boundary

The workflow matrix selects existing catalog/scenario IDs:

| Release architecture | Existing build/evidence route | Package label |
|---|---|---|
| `x86_64` | `x64-nvme-fat32`, `x64-full-stack`, full QEMU gate | kernel + installer/image |
| `aarch64` | AArch64 desktop/Engine2D attested build and QEMU scenario | kernel + FAT32/image |
| `riscv64` | RISC-V64 smoke/display scenario plus serial-shell gate | kernel + FAT32/image |

Each row must run the target-native compiler payload gate and retain in-guest
`simple --version` plus compile/run output. Host-side compile/run does not
satisfy this boundary.

The AArch64 and RISC-V64 deliverables are not called installers until their
bootable installer contract matches x86_64.

## Receipt contract

Each required row uploads one line-oriented receipt:

```text
release_gate_schema=1
release_gate_status=pass
release_gate_platform=<platform>
release_gate_arch=<arch>
release_gate_producer=<command/owner>
release_gate_commit=<sha>
release_gate_version=1.0.0-beta2
release_gate_elapsed_seconds=<number>
release_gate_max_rss_kb=<number>
release_gate_artifact=<relative path>
release_gate_sha256=<hex>
```

Missing keys, non-`pass` status, wrong commit/version, empty artifact, or digest
mismatch fail `release-preflight`. Failure logs are uploaded with `if: always()`.

## Resource regression boundary

The existing stage-4 memory gates remain the absolute safety boundary. The
workflow additionally retains elapsed/RSS receipts by stable runner label.

For the first trustworthy green beta2 run, explicit timeout, runner memory, and
existing absolute gates apply. That run becomes the baseline. Later runs fail
when either metric exceeds the same-runner baseline by more than 10%.
Cross-runner comparisons are invalid.

## Publication boundary

`release-preflight` downloads every required artifact and proves:

- exact expected inventory;
- nonempty files;
- checksum validity;
- payload safety;
- receipt commit/version/architecture match;
- mission-critical `release_blockers=none`.

`create-release` uses `--prerelease` and never updates mutable `latest`.
`verify-release` queries the actual GitHub Release and asserts the exact tag,
prerelease state, workflow commit, and expected asset names. Its failure fails
the workflow and starts a bounded fix cycle.

## MDSOC evaluation

No MDSOC transform or virtual capsule is used. This is build/release
orchestration over existing owners, not runtime composition. A new capsule
would duplicate workflow/platform contracts and increase coupling.

## Consequences

### Positive

- One coordinator and existing platform owners.
- Missing targets or evidence cannot silently publish.
- The GitHub Release itself becomes verified output, not an assumption.
- Resource evidence is comparable without inventing a cross-runner ceiling.

### Negative

- Release latency increases because all rows are hard gates.
- Linux AArch64/RISC-V64 and Windows AArch64 may require emulation or removal
  from executable-package claims until full bootstrap is proven.
- Mission-critical SimpleOS blockers can delay the language prerelease.

### Neutral

- macOS is verified remotely.
- Physical-board claims remain outside this release.

## Startup, hot paths, cache, and invalidation

This feature has no request hot path. Bootstrap caches may accelerate work but
must be keyed by lockfile, source/tag commit, target, backend, and producer
version. A mismatched key invalidates the cache. Release artifacts and receipts
are never restored from mutable caches.

## References

- `doc/02_requirements/feature/next_beta_full_bootstrap_simpleos_multiarch.md`
- `doc/02_requirements/nfr/next_beta_full_bootstrap_simpleos_multiarch.md`
- `doc/04_architecture/app/simpleos/simpleos_multiplatform_build.md`
- `doc/04_architecture/compiler/bootstrap_build_modes.md`
