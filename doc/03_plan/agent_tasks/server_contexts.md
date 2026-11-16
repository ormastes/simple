# Server context ownership

- Lead: Astra server-config lane; interfaces, remote controller integration,
  architecture and final review.
- Sol contract worker: strict decoder/resolver, unit specifications/fixtures.
- Sol transport worker: SSH profile, fixed argv, owned process lifecycle and
  bounded stdio framing; unit specifications.
- Sol host-key worker: OpenSSH Ed25519 encoding, CSPRNG generation, public
  registration/exchange, fingerprint pinning and private-store consumer.
- Root storage lane: retained cross-platform private SSH store and independent
  Windows lead review; owner recovery remains typed and process-local.
- Root Windows transport lane: owned framed-stdin process adapter.
- Sol container worker: immutable pre-sign public environment projection.
- Root Windows container lane: versioned environment and approved network
  policy; address injection alone is not network connectivity.
- Independent reviewer: separate agent after assembled source changes.
- Merge owner: root session, release/1.0.0 PR after review; no release tags.

Shared test helper names: `server_context_fixture_v1`; primary manual flow
labels `Select a shared orchestration server`, `Override a consumer server`.
No passing scaffold placeholders. All authored runtime specs are NOT_RUN.

The full orchestrator goal remains incomplete until authenticated end-to-end
dispatch and cross-host runtime evidence are admitted.
