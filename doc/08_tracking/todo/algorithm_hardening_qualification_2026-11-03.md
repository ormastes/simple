# Algorithm hardening: remaining qualification

As of 2026-11-03, no admitted source-matched Simple runner receipt has been
supplied to this lane. An in-progress P1 build is not admission. Recheck its
producer/runtime/source receipt before executing the existing specs; do not
restart bootstrap, use a Rust seed, or repeat a green acceptance run.

The added TODO rows are **blocked**, not completed. Source repairs, source
reviews, authored SSpec, external reference vectors, and independent fixture
construction do not establish product execution, TDD RED/GREEN, or branch
coverage. Preserve all zero-hit branches and report actual numerator/denominator
per implementation, backend, and target. Missing measurement is UNMEASURED.

## Deduplication

Inspected the canonical `todos` table on release
`f56bfb4237733cf34ebf72501cb033f620b256be`: 431 unique rows, maximum ID 440.
No existing algorithm qualification rows matched these tasks. Existing TODO 413
is XXH3 dual-run shadow retirement; it is a different acceptance criterion and
is preserved. Existing rows were not rewritten and no todo-scan was run. No
bug database or bug status is changed.

| TODO | Qualification target and acceptance | Existing evidence |
|---|---|---|
| 441 | XXH3-128: execute published vectors through both production scope files; validate coverage collector with its uncalled-site fixture; measure at least 99% branch outcomes, explicitly disclosing shared 64-bit logic. | Gate scope `ca902286ba8` in PR 6191 selects two owners and six existing suites but has no measured coverage; `scripts/check/check-hash-algos-coverage.shs`; `test/01_unit/lib/common/crypto/xxh3_128_spec_boundaries_spec.spl`; `test/02_integration/lib/common/hash/xxh3_128_stream_contract_spec.spl`; PR 6075. |
| 442 | gxHash 4.0.0: execute the authored pure-Simple owner and binary caller, compare independent pinned outputs, then measure that owner. Upstream Rust oracle success cannot be used as Simple coverage. | Source `2c8f81fac8a` and follow-up `5e161f9ae96` landed in PR 6191; 160 independent upstream vector comparisons; 164 Simple cases remain UNRUN. Pin the landed source identity before execution. |
| 443 | BLAKE3-256: qualify common and OS owners separately, including keyed input length, derive context, XOF boundaries, binary `ff`, and invalid key sizes. | PR 6075; OS guard `262428fbad4` in PR 6149; reference-vector additions `cfdcc634172` in PR 6174. |
| 444 | X25519/X448: run RFC 7748 positive known answers, field-carry regressions, and SSH all-zero/length rejection through actual owners. | X448 `ad1c28df239` in PR 6149; X25519 guard `996d916a046` in PR 6150; SSH framing `abe2b7b4d0e` in PR 6152. Full curve KAT qualification remains owed. |
| 445 | RSA-PSS/ECDSA: execute positive signature oracles, malformed framing and scalar cases, and extreme PSS dimension checks without arithmetic overflow. | RSA `5896e4cb532` in PR 6149; signature specs `01730e25e42` in PR 6150; ECDSA `b43ecc38958` in PR 6174. |
| 446 | ChaCha20-Poly1305: execute RFC 8439 known answers and key/nonce rejection, then verify error propagation and record sequence behavior through real TLS/SCV callers. | Decrypt `93e201c08b3` in PR 6150; checked API `81fd968be8d` in PR 6153. Caller migration is an assigned design/implementation dependency, not a permission blocker; source guards alone do not prove checked-error reachability. |
| 447 | SQLCipher 4: execute independent KDF/HMAC/page oracles, authenticate before interpretation, require reserve 80 for the selected encrypted profile, and retain ordinary SQLite reserve-zero compatibility. | `dbc9480233c` in PR 6150; fixtures `2e20a20da72` and guard `4344e615e1f` in PR 6152. Independent fixture validation is not Simple storage-owner execution. |
| 448 | Native OS AES: remeasure the actual AES-128 wrong-output and AES-256 provider/link failures, then verify real authenticated decryption and negative tags. | `doc/08_tracking/bug/os_crypto_native_failures_2026_10_31.md`; `test/fixtures/devhub/native_os_crypto_kat/main.spl`. Current C-scalar and OpenSSL bridge results do not qualify these owners. |
| 449 | WebSocket: execute strong-entropy nonce/mask acquisition and real entropy-failure propagation, not only deterministic wire fixtures; verify all 32 mask bits at callers. | RFC 6455 sections 4.1 and 5.3; `f2c3f80419f` in PR 6149; full-width mask `4bd876d4280` in PR 6174. |

## Retained measured evidence and exclusions

AES C scalar already has 138 passing assertions: **AES-only 155/156** branch
outcomes. The larger extracted slice is **157/158**, including two unrelated RSA
fallback outcomes; do not interchange those denominators. OpenSSL owned bridge
has a 97/112 baseline and a one-extension 112/112 measurement with 208 assertions
and 15 genuine EVP error injections. That is bridge coverage, not libcrypto
internals, AES-256, Simple, or full-runtime ABI qualification. Tests landed in
PR 6174; do not rerun them merely to refresh a ledger.

Retained local artifacts:

- `C:/dev/p3new/hash-coverage-20261103/aes-cycle1/artifacts.sdn`
- `C:/dev/p3new/crypto-protocol-20261103/aes-openssl/coverage-extension/artifacts.sdn`
- `C:/dev/p3new/hash-coverage-20261103/completion_matrix.md`
- `C:/dev/p3new/hash-coverage-20261103/coverage_plan.md`

Each TODO completes only with owner-matched executable evidence, current spec
manuals generated by an admitted runner with zero stubs, and a reviewed coverage
report where coverage is required. Do not close canonical bug records from TODO
bookkeeping. Optional NEON/RVV acceleration and new compression features are not
added to this correctness/qualification scope.

