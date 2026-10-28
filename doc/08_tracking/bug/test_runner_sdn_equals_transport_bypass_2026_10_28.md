# Equals-form SDN flag bypassed public transport admission

`parse_private_sdn_worker_args` recognized `--sdn` and `--format sdn`, but
forwarded `--format=sdn` as an ordinary argument. The latter entered the legacy
console result formatter: spec-only runs could crash during serialization,
doc-only runs emitted no SDN document, and mixed runs emitted the spec summary
before doctests finished. It also bypassed the public/private flag-mixing
rejection for an authenticated private worker.

Recognize all three public spellings at the same parser boundary. The native
regression checks equivalent forwarding, rejects each public spelling mixed
with an authorized private worker, rejects an unauthorized worker, and retains
the valid authorized-worker contract.

Do not add direct console SDN output to evade this boundary. The existing public
wrapper requires scoped child environment and process-group retirement, and
currently fails closed when the provider cannot meet its contract. Neither the
V4 admission guard, wrapper, nor main dispatch is changed. Public SDN remains
unavailable on that provider; consistent rejection is not successful test
execution. An observed baseline `--sdn` invocation returned the structured
failure `SDN worker scoped-environment process provider is unavailable or
insufficient`, while `--format=sdn` entered normal execution.

Validation: the native baseline fixture fails with `equals SDN flag bypasses
public transport`; the corrected two-module native fixture passes all alias,
mixing and authorization cases. Final binary SHA-256:
`c9e2757611cb234331f140504edcb5d3740338d0a879f12e6e4a4b81ba909d5e`.
Build `test/fixtures/test_runner_sdn_args/main.spl` with the selected native
compiler, then run `scripts/check/check-native-sdn-args.shs --binary PATH`.
Local receipts are under `/tmp/runner-source-routes-evidence-20261028/sdn-args-*`.
Full rebuilt-runner acceptance is separate from this native parser proof.
