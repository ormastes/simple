# Hosted WM runtime DSO lacks trusted production build provenance

Status: open

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

## Resolution note (2026-11-05, work/libbug-linux-wmdso-20261105)

Root cause: `bootstrap_runtime_provider` in
`scripts/check/check-linux-hosted-wm-live-window-evidence.shs` refused a copied
bootstrap DSO only by path prefix or by live content comparison against the
canonical `src/compiler_rust/target/bootstrap/deps/libsimple_runtime.so`. When
that canonical artifact is absent from the checkout (the default on a clean
tree — only `libsimple_runtime.a`/`.rlib` ship), both checks silently skipped,
so a bootstrap DSO copied from elsewhere passed admission with any
caller-supplied matching SHA-256.

Fix (wrapper-only, no browser core / TLS / runtime path changes):

- New persistent forbidden identity registry
  `config/check/hosted_wm_forbidden_runtime_identities.sdn` records SHA-256
  content digests of known Rust-seed/bootstrap `libsimple_runtime.so` builds
  (10 aarch64 build-tree digests recorded 2026-11-05). Rows are cumulative.
- `admit_runtime_provider` now: requires the registry to exist (fail-closed
  `runtime-provider-forbidden-registry-missing`), computes the provider digest
  before the bootstrap check, and refuses the provider when its digest matches
  the canonical artifact (when present) or any registry row, in addition to
  the existing bootstrap path-prefix rule.
- The accepted receipt records the registry path and its SHA-256 alongside
  the existing provider path/hash/build-identity/admission fields.
- Self-test gains fixtures: copied bootstrap DSO refused with the canonical
  artifact absent (registry hit), missing registry fail-closed, and a
  legitimate non-bootstrap provider still admitted without the canonical
  artifact.

Verified: harness extracted from the wrapper shows a copied real bootstrap
DSO now rejected (`runtime-provider-bootstrap-forbidden`) with and without the
canonical artifact, a legitimate provider admitted, and the missing registry
failing closed; `--self-test` passes. Remaining per the doc: this closes the
copied-DSO admission gap, but a trusted production provider build manifest
(e.g. the pure-Simple runtime build recording its provenance into the
registry) is still future work; the receipt remains blocked evidence for
REQ-WEB-BROWSER-011/014 and NFR-WEB-BROWSER-011/015 until that exists.
