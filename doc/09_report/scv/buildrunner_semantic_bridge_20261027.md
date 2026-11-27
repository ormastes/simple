# BuildRunner semantic validation bridge lane

Owner: Codex `/root/impl_solver_host`, session 2026-10-27.
Base: `8dcbbbf949c`.
Worktree: `/tmp/simple-scv-buildrunner-semantic-20261027`.
Branch: `work/scv-buildrunner-semantic-20261027`.

Uses implementation/coding skills and `/tmp/scv-buildrunner-current-research-20261027.md`. Scope: new common compiler contract, narrow concrete driver semantic adapter and dedicated authored specs only. No existing scheduling, BuildRunner CLI, compiler provider or owner modules change.

Parent approved a bounded request/provider/result bridge using the existing `SemanticQueryReadManifestV1`. The concrete implementation must delegate to `CacheGatewayAdapterV1` and `SemanticScopeLiveOwnerV2` with actual opaque owner handles. Source receipts do not supply semantic authority. Unsupported/incomplete/absent authority remains an explicit cache miss.

User deferred Phase 3 execution. No compiler/check/test/docgen/builder invocation, runtime proof, performance measurement, push or merge occurs in this worker lane. Parent owns integration and later qualification.

Implemented source: common bounded request/provider/outcome contract and concrete existing gateway/live-owner adapter. The common facade re-verifies actual frozen-source witnesses, receipt, raw bytes and recorded SQR1 inputs. The adapter delegates to actual owner grant/result validation, verified pinned CAS objects and existing action catalog, and compares all recorded read fields with the actual owner-projected read set. Byte allowance continues across request and CAS stages; one-to-one source mapping prevents duplicate relative paths from covering a different file.

Astra source review identified that canonical source-byte equality alone does not bind requested SCV namespace/path policy/configuration/target/runtime to the compiler semantic snapshot. The adapter now conservatively returns `Unavailable("semantic-nonsource-authority-relation-unavailable")` after matching diagnostics. No actual production `Verified` return, caller-created grant, public attestation or hash-domain translation exists. The shared `Verified` contract remains reserved for a future actual authority-backed relation; `full_artifact_authorized` is always false.

Authored specs use real SCV snapshot/witness owners and actual semantic adapter/owner objects. Complete-labelled caller manifests are negative controls only. Current CLI has no actual semantic manifest/opaque handles and does not call the seam. Final authority relation, issuer/worker availability, consumer wiring and native qualification remain required pending work.

One static pass: staged whitespace check passed; direct-env runtime guard `--working` and `--staged` each passed; executable `_spec.spl` count under `doc/06_spec` was `0`. No native check/spec/docgen/coverage or production-readiness PASS is claimed.
