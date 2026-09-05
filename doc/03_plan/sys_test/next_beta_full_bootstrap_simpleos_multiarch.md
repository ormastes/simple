<!-- codex-design -->
# System Test Plan — Next Beta Full Bootstrap and SimpleOS Multiarch

## Scope

Prove the release source contract, full-bootstrap evidence contract,
three-architecture SimpleOS artifact contract, resource receipts, and actual
GitHub prerelease inventory for REQ-001..REQ-005.

Physical-board proof and AArch64/RISC-V64 installer claims are excluded.

## Executable spec

`test/03_system/app/release/next_beta_full_bootstrap_simpleos_multiarch_spec.spl`

Generated manual:

`doc/06_spec/03_system/app/release/next_beta_full_bootstrap_simpleos_multiarch_spec.md`

## Environments

- Local Linux x86_64 with GNU time, QEMU x86/AArch64/RISC-V, LLVM, mtools,
  dosfstools, OVMF, and FreeBSD QEMU prerequisites.
- Native GitHub macOS and Windows runners.
- Authenticated GitHub CLI only after explicit push approval.
- Pure-Simple `simple-core` or `core-c-bootstrap` for SPipe/docgen; Rust seed is
  not accepted.

## Execution order

1. Run the focused source-contract spec.
2. Run local full bootstrap and memory gates.
3. Run SimpleOS x86_64, AArch64, and RISC-V64 gates.
4. Run FreeBSD QEMU full bootstrap.
5. Run whole tests once.
6. Run production verification.
7. After approved push, require all GitHub matrix rows and `verify-release`.

## Pass/fail

Any missing marker, fallback, artifact, receipt, digest, measurement, embedded
compiler proof, mission-critical proof, matrix success, or GitHub asset is a
failure. Skips do not satisfy a release target. `release_blockers` must equal
`none`.

## Manual policy

Primary scenario steps are visible in this order:

1. Validate immutable beta2 identity.
2. Prove full self-hosted bootstrap.
3. Build and boot SimpleOS release targets.
4. Check resource regression receipts.
5. Publish and inspect the GitHub prerelease.

Executable source is folded. Platform matrix detail and failure cases are
folded. Evidence kind is `artifact`, `exec`, or `log`; captures link to retained
workflow artifacts rather than embedding large logs.

## Traceability

| REQ | Behavior | Executable cases | External evidence | Coverage |
|---|---|---:|---|---|
| REQ-001 | immutable beta2/tag/prerelease identity | 3 | `check-version`, GitHub release JSON | Full |
| REQ-002 | fail-closed whole-platform full bootstrap | 3 | per-row binary/receipt/log | Full |
| REQ-003 | x86_64/AArch64/RISC-V64 SimpleOS targets | 3 | QEMU/compiler/package receipts | Full |
| REQ-004 | memory/performance gates and baseline | 3 | stage-4 logs and metric receipts | Full |
| REQ-005 | preflight, publication, post-publish audit | 3 | workflow result and release asset JSON | Full |

## Risks

- Concurrent dirty bootstrap/memory files may own required fixes.
- Cross/emulated full bootstrap may expose unsupported code generation.
- Mission-critical SimpleOS formal gates may require host dependencies.
- GitHub-hosted runner variance can invalidate comparisons; only exact runner
  labels are compared.
