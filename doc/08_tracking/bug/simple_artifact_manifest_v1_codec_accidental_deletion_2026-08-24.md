# SimpleArtifactManifest v1 codec accidental deletion

Status: restored, static review pending; runtime verification intentionally deferred.

Commit `9eef0f3623a` introduced the canonical `SAM1` signing-byte codec. Commit
`00ecd3367c1`, whose stated scope was the frontend-cache pool snapshot, deleted
the codec and its focused spec without replacing the API or changing the wire
format. The current loader signature verifier imports that missing module.

The restoration retains the established byte order and `SAM1` envelope, so
existing signing inputs remain stable. Acceptance is reconciled with the newer
installed-manifest bounded-value contract: collection, element, aggregate, and
signing-body ceilings now fail closed before encoding. The original exported
limit names remain compatibility aliases to those authoritative bounds.

No tests, builds, SPipe, bootstrap, optimizer, or benchmarks were run for this
recovery, per the active user instruction. Focused runtime verification remains
required before release.
