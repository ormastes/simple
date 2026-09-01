# Unified SCV/JJ/Git/DevHub/Spipe lifecycle
<!-- # @ac: AC-16 -->

The base implementation is deliberately observe-only. Use:

```text
devhub lifecycle capabilities
devhub lifecycle policy-check .spipe/policy/vcs.sdn
devhub lifecycle version-check release/version.sdn
devhub lifecycle version-explain release/version.sdn
devhub lifecycle inspect change chg_example idempotency-key
```

These commands inspect the typed `devhub/v1` lifecycle surface and validate
protected-ref policy. They do not update refs, publish reviews, create tags, or
release artifacts. Typed SJ `IntegrateRequest` planning is currently a library
surface; it admits only exact revision, CAS, current approval, complete gate,
policy, actor, and authority inputs and still labels dry-run plans explicitly.

Authority remains SCV lifecycle identity/evidence, JJ local editing, Git public
transport, SJ protected-mutation planning, DevHub provider UX, and Spipe
orchestration. Existing compatibility commands remain supported.

Lifecycle records are digest-bound `scv-lifecycle/1` envelopes stored beneath
`.scv/lifecycle/`. Provider capability records refuse strict operations a
provider cannot represent; non-strict projections label semantic loss rather
than presenting an ordinary comment as an equivalent blocking verdict.

Do not bypass the typed plan with raw Git/JJ mutation. The base policy declares
server enforcement as required evidence; actual remote enforcement and mutation
promotion remain later stage gates.

## Delivery and verification status

The agent-base implementation is available on public `main` at Git commit
`5cd33eca7717a7b87856a001fdb4f72deacfe00d`. Its publication used an explicit
user-authorized `--no-verify` push because the available `bin/simple` was the
Rust bootstrap seed rather than an admitted pure-Simple CLI.

Interpret that state precisely:

- the observe-only APIs and documents are delivered;
- focused seed runs are diagnostic only;
- no authoritative verification receipt exists for this delivery;
- `--no-verify` does not promote SCV, enable protected mutation, approve a
  review, satisfy a release gate, or authorize future bypasses;
- any authority-promotion change must first produce fresh evidence with an
  admitted pure-Simple CLI.

The outstanding commands and provenance requirement are recorded in
`.spipe/scv_jj_git_devhub_spipe_unified_lifecycle/state.md`.

## Safe operator sequence

1. Run the observe-only `capabilities`, `policy-check`, `version-check`, and
   `inspect` commands above.
2. Preserve the returned schema, digest, revision, policy, and idempotency IDs
   in the change evidence.
3. Treat any stale revision, incomplete bundle, unknown policy, corrupt store,
   or unsupported provider semantic as a refusal.
4. Before enabling a mutation or publication adapter, obtain the missing
   authoritative evidence and satisfy that plan stage's exit gate.
5. Never convert the historical no-verify publication waiver into a reusable
   approval or gate result.
