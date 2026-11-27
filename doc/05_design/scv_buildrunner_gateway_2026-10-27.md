# BuildRunner and read-only GitHub gateway Phase 3 design

**Status:** readiness design only. Phase 3 implementation acceptance runs were deferred by the user and are **NOT RUN**. The interface contracts below were coordinated from isolated implementation worktrees; they are not claimed to be integrated into this documentation worktree, compiled, or behaviorally qualified. A source definition or successful source compile is not runtime behavior evidence. SSpec and the generated manual are not created here; manual is N/A until the SSpec is authored and generated later.

## Goal and boundary

Prepare two independently testable read paths: BuildRunner reuses only outputs whose task identity, source evidence, and existing output receipt all validate; the gateway serves authenticated, allowlisted, read-only GitHub objects. The gateway is not a publisher. Do not infer a complete GitHub source tree from an individual object read: the coordinated V1 protocol supports `capabilities`, `read_ref`, `read_commit`, and `read_blob`, but no tree enumeration operation. A complete `ScvSnapshotV2` for a build must come from a complete admitted inventory; remote GitHub reads can supply only explicitly requested immutable objects until a complete inventory contract exists.

## BuildRunner source evidence

The coordinated binding is `app.buildrunner.scv_admission_v1.BuildRunnerScvAdmissionV1`, carrying the task and identity, `CompileSnapshotV1Adapter`, requested `ScvSnapshotV2`, declared source inputs/witnesses, `VerificationReceiptV1`, `source_only`, and an admission digest. `build_runner_scv_bind_v1(task, adapter, witnesses)`, `revalidate_v1(binding, requested_snapshot)`, and `admission_digest_v1(binding)` bind exact declared input paths/bytes and reconstruct the expected subject. Use the existing names `ScvSnapshotV2`, `DirectoryWitnessV1`, `ScvSourceWitnessV1`, `VerificationReceiptV1`, and compiler-owned `SemanticQueryReadManifestV1`; do not create another snapshot owner, scheduler, or semantic manifest.

The V1 adapter accepts only a validated, non-drifted compile snapshot and complete inventory. Inventory generation does not prove an event acknowledgement barrier; nonzero acknowledgement is refused. Source witnesses cannot establish configuration, external/generated inputs, compiler semantic reads, aliases, mode changes, or complete event coverage unless separately covered by their owning issuer. Unsupported or incomplete correspondence refuses source reuse. The resulting receipt remains `source_only=true`: it can prove source observations for a requested snapshot but cannot admit a cached OBJ/BIN/LIB by itself. BuildRunner must retain its existing independent task identity, producer/toolchain/environment policy, task result, reaped worker, and output digest checks.

The later production insertion point is the BuildRunner parent run, before journal replay/cache resume and before dispatch: capture/validate one frozen binding under the existing run lock; carry it through revalidation, recovery, and worker staging; use exact frozen bytes for declared source inputs. The transport may stage only exact witnessed task inputs from that frozen root; current unsupported links or outputs remain a refusal. Never mutate process-global compiler authority environment or let workers refresh `CURRENT`.

## Read-only gateway

Configuration uses strict SDN. Repository configuration APIs are `scv_config_parse_v1`, `scv_config_load_v1`, `scv_config_route_v1`, and `scv_config_effective_v1`; gateway service configuration is separately `ScvGatewayConfigV1`, parsed by `scv_gateway_config_parse_v1` / `scv_gateway_config_load_v1`. Credentials are env references, not SDN plaintext. A service listens only on literal `127.0.0.1`; absent TLS support, normal service mode refuses. Plain HTTP is permitted only with explicit `--development-loopback --reason TEXT`; that mode is local-only and is not operational TLS evidence.

Protocol messages are versioned, bounded SDN with exact request binding: version, id, logical repository, method, and ref/OID. Responses must match the expected request and allowed logical repository, and publication must equal `not_publication`. Payloads use lowercase hex bounded to 1 MiB; protocol payload SHA-256 is source-integrity evidence only. The GitHub provider `scv_gateway_github_read_v1(policy, request, DbGithubTransport)` permits reads only. Server-owned allowlist maps logical repository to `github.com/owner/repository/numeric_id`; immutable numeric-ID routes use pre-read and post-read identity probes. Blob responses require strict base64 decoding, size checks, and recomputed Git blob SHA-1. Commit validation checks the requested SHA field only; it is not a raw commit-object cryptographic proof. JSON exists only at the GitHub REST boundary. No upload, ref update, PR, or publication call is reachable through this service.

## Required component behavior

1. Freeze source once per BuildRunner run; record snapshot ID and source-only receipt in existing run state. Revalidate before warm receipt reuse, after recovery, and before accepting outputs. Source mutation or unknown coverage means miss/refusal.
2. BuildRunner warm reuse requires both source binding and the independent existing result/output receipt. Missing output may use only the already verified local attempt restoration path until a separate admitted artifact store exists.
3. Gateway request auth and repository allowlist checks happen before provider calls, including capabilities and any cache path. Reject duplicate auth headers and duplicate/unknown protocol fields.
4. Bind each GitHub reply to the exact request ID, repository, method, and ref/OID. Validate status/object-kind consistency and all size bounds before returning bytes.
5. Never claim GitHub full-source coverage from `read_blob`; never claim raw commit integrity from the SHA-field match; never label local-development HTTP as secure remote transport.

## Independent evidence owners after interfaces are frozen

- BuildRunner caller owner: only `src/app/buildrunner/**` and transport staging, preserving the parent-owned `std.common.task_runner` scheduler.
- Gateway owner: only `src/app/scv/gateway_*` service/config/commands and protocol/provider adapter boundaries.
- Test owner: separate acceptance specs and fixtures, with no production code edits.
- Compiler semantic-read binding stays with compiler ownership; no duplicate `SemanticQueryReadManifestV1` and no changes on the frozen compiler phase branch.

These are later ownership boundaries, not completed assignments or implementation evidence.
