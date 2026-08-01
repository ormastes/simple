# Release Beta Architecture

The release is a fail-closed evidence pipeline. A source revision first produces a strict bootstrap chain; only the admitted Stage 4 full CLI may produce command, test, MCP/LSP, and package evidence. Platform artifacts remain separate until an aggregate receipt proves every selected non-macOS row and then permits GitHub release publication.

<!-- sdn-diagram:id=release_beta.architecture -->
<details class="sdn-source"><summary>SDN source</summary>

```sdn id=release_beta.architecture hash=sha256:auto render=ascii
@layout dag
@direction LR
SourceRevision -> StrictBootstrap
StrictBootstrap -> FullCliAdmission
FullCliAdmission -> ToolQualification
FullCliAdmission -> PlatformMatrix
ToolQualification -> PublicationGate
PlatformMatrix -> PublicationGate
PublicationGate -> GitHubRelease
GitHubRelease -> RemoteAttestation
RemoteAttestation -> FinalReadiness
```

</details>
<details class="sdn-ascii" open><summary>Diagram</summary>

```ascii generated-from=release_beta.architecture hash=sha256:auto
SourceRevision -> StrictBootstrap -> FullCliAdmission -> ToolQualification -+
                                             +-------> PlatformMatrix -----+-> PublicationGate -> GitHubRelease -> RemoteAttestation -> FinalReadiness
```

</details>
<!-- sdn-diagram:end -->

## Layers

| Layer | Owner | Responsibility |
|---|---|---|
| Compiler resolution | `src/compiler/20.hir/hir_lowering/` | Preserve imported facade names with bounded cyclic traversal. |
| Candidate production | `scripts/bootstrap/bootstrap-from-scratch.sh` | Produce provenance-bound Stages 2–5 with fallback disabled. |
| Candidate qualification | `scripts/check/check-bootstrap-essential-tools-smoke.shs` | Prove the fresh full CLI actually runs core tools. |
| Tool attestation | `scripts/check/record-release-beta-essential-tools.shs` | Retain the canonical smoke log and bind its markers to the exact Stage 4 digest. |
| Payload qualification | Existing release checker scripts | Validate sizes, strip state, archive safety, notices/fonts, checksums, and MCP/LSP identity. |
| Platform orchestration | `.github/workflows/release.yml` | Build all selected rows, transfer named artifacts, and prevent downstream publication after any required failure. |
| Native FreeBSD gate | `scripts/check/check-freebsd-bootstrap-qemu.shs --full` | Prove the pure-Simple bootstrap inside a fresh FreeBSD VM; cross-compilation alone is insufficient. |
| Platform attestation | `scripts/check/collect-release-beta-platform-evidence.shs` | Validate seven downloaded executable archives and derive the platform receipt from embedded provenance. |
| Evidence/manual | `test/03_system/app/release/`, `doc/06_spec/` | Present operator-readable scenario flow and AC traceability. |
| Remote attestation | `scripts/check/record-release-beta-github-evidence.shs` | Query the completed GitHub run and published tag; write provenance-bound remote evidence. |

## Decisions

- D-1: Stage 4 is the sole authority for release command/test evidence; Stage 2, the Rust seed, and stale deployed binaries are diagnostic only.
- D-2: Every selected non-macOS beta row is an executable role. Missing binaries fail the producer; source-only output cannot be uploaded under an executable artifact name.
- D-3: Facade-glob traversal uses a per-root shallowest-depth memo so cycles terminate without shrinking the existing depth-limited reachable set.
- D-4: Platform producers upload separately named artifacts; the aggregate release job depends on every selected producer and validates contents before publication.
- D-5: Local wrappers and the GitHub workflow share the existing checker owners rather than duplicate package or QEMU logic.

## Interfaces

- `strict_bootstrap_candidate(source_revision) -> Stage4CandidateReceipt`
- `release_checker_contract(candidate, artifact) -> CheckReceipt`
- `release_workflow_platform_matrix(version) -> [PlatformArtifactReceipt]`
- `release_artifact_receipt(version, candidates, checks) -> ReleaseReceipt`

No new runtime boundary or public language API is introduced.
