# Hosted WM runtime DSO is absent from security evidence admission

Status: open

## Finding

`scripts/check/check-linux-hosted-wm-live-window-evidence.shs` rejects a Rust
seed `SIMPLE_BIN` and admits `HOSTED_WM_ARTIFACT` by SHA-256, but defaults
`SIMPLE_WM_RUNTIME_LIB` to
`src/compiler_rust/target/bootstrap/deps/libsimple_runtime.so` and injects that
DSO with `LD_PRELOAD` without recording or admitting its identity.

The resulting receipt cannot prove that the admitted hosted browser artifact
ran with the claimed production runtime provider. It must remain blocked
evidence for REQ-WEB-BROWSER-011/014 and NFR-WEB-BROWSER-011/015.

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
