# Host metadata listener runtime — authored manual

STATUS: NOT_RUN. Authored source specifications; no runtime, test or build execution and no generated evidence.

| Exact step | Status |
|---|---|
| retains actual listener owner and closes the same journal before transport | NOT_RUN |
| keeps real lease mismatch cleanup-only and retries the exact carrier before listener stop | NOT_RUN |
| retains partial open as blocked and reports its original error after actual cleanup | NOT_RUN |
| keeps partial transport locally recoverable on actual journal close failure without promoting phase4 | NOT_RUN |
| preserves installed mapper error order without a live domain argument | NOT_RUN |
| rejects actual missing pinned policy before acquiring a domain or transport | NOT_RUN |

HOST-SERVICE-RUNTIME-01 covers actual installed mapping reuse, native SDK listener owner retention and partial-open provenance. HOST-SERVICE-RUNTIME-02 covers same owned journal writer-first close, real lease-mismatch failure, canonical cleanup retry and no stale WAL in cleanup-only callbacks.

The fixture reuses the actual signed-policy/private-root/owned-WAL setup and calls the real SDK listener opener. Its existing Container and root observations are explicitly scripted. It does not qualify the public production root bootstrap, native enrollment, kernel peer credentials, response-send failure, consumed/unknown native close injection, fresh service incarnation, Windows native privacy, provider effects or control-loop latency. Direct SDK request values are explicit frame fixtures, not authenticated native peers. The one public runtime-open negative exercises missing pinned policy before domain/listen. Positive production runtime-open and pre-Ready partial journal cleanup remain NOT_RUN/unqualified.

The single parent must replace runtime on every turn; copying a value does not prove uniqueness. Ready denotes only current Linux finite-root metadata transport/domain open, not future V2 fresh-service/quarantine readiness or Simple Container effect enablement. Partial phase4 is trusted-local cleanup only. A fully opened phase1 service retains authenticated cleanup-only status after failed writer close. Physical transport closure with nonempty prior error is still an error, never clean stop success.
