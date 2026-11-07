# Controller/container V2 wire test scope

Eight SSpec cases and one reusable fixture target the actual controller dispatch,
host execute, helper plan and controller reply codecs. Production app/core design
is owned separately; this file records TEST scope only. No production source edits.

## Reviewed source snapshots

- `src/lib/common/contracts/orchestration/controller_dispatch_request_v2.spl`: `f2f44dd646cdf14bc9c849a7a67bc31e5c1e765e38aa50451fb078e9e55fce6f`
- `src/lib/common/contracts/orchestration/host_execute_request_v2.spl`: `9083202d0e5cc5542d49e5d0e65b05517149c337bc26732737527594a096a505`
- `src/lib/common/contracts/orchestration/host_helper_plan_v1.spl`: `816e79a0beb36cef4bf6e19cc858528ad3bbe6ef650a17cf181f935f8ae8a46d`
- `src/lib/common/contracts/orchestration/controller_execution_reply_v2.spl`: `fa1717029bce3107279671ae55869d9b413b07cc03dfafc9411ec6d4074c8978`

Fixture construction adapts the prior V1 actual assignment, host reservation
receipt and real Ed25519 signing-message helper patterns. There are no zero-proof
successful authority tests. The codecs themselves never authorize signatures;
frame signing is not a protected publisher registry or live grant decision.

Linux input uses the existing actual canonical retained-request encoder and
semantic digest implementation. Windows input is explicitly opaque common-wire
fixture data: backend/service-mode roundtrip does NOT claim valid Docker provider
schema, native availability or Windows execution. Those platform semantics stay
with real leaf/host acceptance. No fake SimpleContainerOwner or stub provider is
constructed, no journal mutates and no process/container executes in this suite.

Cases cover lossless four proof-pair retention; full V2 scope hash with distinct
physical alias/native machine and honest service mode; exact UID/host operation;
proof renewal preserving Linux retained bytes/semantic identity/plan/assignment;
actual prepared-receipt integrity refusal; mandatory aggregate parent-budget digest
and unique helper operation; strict packets; correlated reply hash/false completion;
and nested/outer UTF-8 bounds. Step names exactly mirror case titles.

The helper plan pins the digest of an actual canonical ControllerParentBudgetV1
fixture referring to the SAME parent operation/assignment. A different valid
digest changes helper identity, but the helper codec cannot know approved budget
membership. Host must load/verify that budget and atomically account parent plus
helpers in its existing physical ledger before effects.

No P0/P1 defect was found within these documented integrity-only codec boundaries.
The reply intentionally hashes opaque nested host bytes; consumer must decode and
check expected complete host scope before use. A self-consistent canonical packet,
prepared receipt, real signing frame or renewed proof is not completion authority.
Actual app/host dispatch, fresh-clock signature validation, protected ownership,
capacity accounting and provider nonce/native-identity checks remain integration
gates. Runtime/admitted SSpec/manual generation/coverage: NOT_RUN. No build/retry.
