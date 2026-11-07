# Native Item5 app manifests did not bind runtime authority

Status: source repair and metadata regressions prepared; no Simple application
qualification is claimed.

Affected owner: `scripts/check/lib/item5-app-build-manifest.pl`, native
`item5-simple-app-build-v2` validation. The caller is
`scripts/check/run-item5-app-vector-receipts.shs`. The matched performance
runner additionally compares the Hello runtime against its measurement runtime,
but the functional app manifest previously carried no enforced runtime binding.

## Reproduced failure

On source `41d9151614adbaadb098b871894537e90593a70f`, the native validator
accepted a synthetic negative case with a valid-shaped Hello runtime hash of
64 `c` characters and a top-level manifest plus all four app runtime hashes of
64 `f` characters. It returned exit 0 and the normal four-column provenance
output. Compiler, source and binary-hash metadata otherwise agreed.

This proves that the checker ignored explicitly conflicting runtime authority.
It does not prove which runtime was used to build any real application.
Original counterexample inputs and actual output are retained under
`build/review/item5-native-runtime-binding-counterexample-20261107/`.

## Repair and compatibility

Native v2 now requires a scalar lowercase 64-digit SHA256 in the Hello receipt,
the same `runtime_archive_sha256` in the top-level app manifest, and the same
hash in every requested app entry. Compiler/source/binary checks and the
four-column output remain unchanged. The existing v2 contract is tightened;
there is no new schema, archive fallback, fabricated admission or historical
Hello conversion. Old native manifests missing runtime fields are rejected.

Cross-target v3 remains distinct: the target archive is bound to the explicit
target invocation and per-app target metadata. It need not equal the host
runtime used by the producer Hello. A positive regression explicitly supplies
different host and target runtime hashes.

The two tracked native-v2 fixture writers were updated coherently:
`test-item5-app-build-manifest.shs` and
`test-item5-app-vector-receipt-runner.shs`. No tracked production manifest
constructor was found; manifests remain captured caller provenance. The
canonical runner help now documents the required native fields.

## Verification and limits

The native manifest regression passed one valid case and rejected 26 cases,
including missing/invalid/structured Hello runtime, missing/wrong/invalid
top-level runtime and missing/wrong/invalid runtime for each of the four roles.
Existing compiler/source/tree/status negatives remain covered.

The v3 metadata regression passed nine profile/loop models, rejected its 15
existing negative cases, and accepted the new distinct-host-runtime case.
It did not execute QEMU. Parser/staging preflight checks also passed with the
updated native fixture data; no Simple app or provider kernel executed.

Initial verification was blocked before cases ran by Windows checkout CRLF
being interpreted by the Linux shell. LF Git-equivalent private materialization
resolved that environment issue. The runner preflight then encountered an
omitted unchanged receipt helper after its nested native regression had passed;
the remaining unit checks were continued without repeating that native check.
Both original failures are retained. Evidence is under
`build/review/item5-native-runtime-binding-verification-lf-20261107/`.

This checker verifies declared identity consistency. Actual compile commands,
runtime archive bytes, current pure producer lineage, real Hello execution,
functional quartet execution and matched application measurements still require
their independent receipts. CUDA, target hardware, performance and bootstrap
readiness are not qualified by these synthetic metadata regressions.
