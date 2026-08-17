# Hosted WM runtime DSO lacks trusted production build provenance

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 01).

## Finding

`scripts/check/check-linux-hosted-wm-live-window-evidence.shs` now rejects a
Rust seed `SIMPLE_BIN`, requires an explicit runtime path and SHA-256, rejects
the canonical/current copied bootstrap content, launches a private admitted
copy through inherited fd 9, and records the runtime/content/admission
identities.

One production blocker remains: if the canonical bootstrap DSO is absent, the
wrapper has no trusted provider build manifest or persistent forbidden
bootstrap identity. A bootstrap DSO copied from elsewhere can therefore still
be presented with a caller-supplied matching hash.

The resulting receipt proves the exact launched bytes but not their production
build provenance. It must remain blocked evidence for REQ-WEB-BROWSER-011/014
and NFR-WEB-BROWSER-011/015.

## Owner and fix boundary

Owner: `scripts/check/check-linux-hosted-wm-live-window-evidence.shs`.

Do not change the browser core or add another TLS/runtime path. The wrapper must
require an admitted non-bootstrap runtime provider, record its path, SHA-256,
build identity, and relationship to the hosted artifact, and fail closed on a
missing, bootstrap, stale, or mismatched provider.

## Acceptance

1. A deliberate bootstrap-runtime fixture is rejected.
2. A missing or hash-mismatched runtime is rejected.
3. The accepted receipt records hosted binary and runtime path/hash/build
   identity without exposing secrets.
4. The production security SSpec binds its sandbox/TLS evidence to both
   admitted identities.
5. The pure-Simple runtime and hosted artifact produce the live sandbox/TLS
   evidence; a Rust seed or bootstrap DSO never qualifies.
