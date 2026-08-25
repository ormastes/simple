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
