# Executed-access outer API remains required

Status: production composition migration implemented; admitted-runtime proof pending

The fixed executed-access registry now admits only a canonical extraction,
publishes a physical `EnvExecutionReceiptV1`, authenticates operation/opcode/
capability/trace/generation, consumes exactly once, and terminally poisons a
failed invocation. The previous wrapper-side metadata synthesis is removed.

The five buffer operations now expose untagged owner calls that own
`issue -> physical execution -> publish -> tagged replay dispatch`. They derive
successful status from the physical receipt, bind the exact captured arrays by
the canonical digest, and keep tagged/raw/direct/compare leaves private.
The hosted physical adapter now lives at the application-level production
composition point, `app.hal_provider.environment_executor`; the former
`app.test` path is only a compatibility re-export. The shared init-owned
`HalBufferExecutionOwnerV3` in `app.hal_provider.buffer_execution` is the sole
application caller of all five outer APIs. It passes preparation-owned
executors and caller-owned argument/capture/output arrays through unchanged.
No ambient operation was moved into `src/lib`.

Completion requires proving the route with an admitted runtime. The hot path
must remain bounded, allocation-free after owner initialization, and must never
retry an invocation after a physical effect or poisoned publication.
