# Slang S3 independent request-context implementation report

Date: 2026-09-08. Status: native PASS; Simple-language check unavailable.

Implemented one resident model with a bounded table of request-owned llama
contexts, samplers, prompt/output/token buffers, cursor state, and prefix
leases. Positive generation-tagged handles reject stale and prior-slot
identities. The legacy S1/S2 ABI delegates to a counted compatibility request.

The complete optional request ABI is admitted atomically on the Simple side.
Generation uses independent requests when that group and capability bit are
present, and otherwise retains the S2 path. Native busy teardown is propagated
before dynamic-library unload.

Focused evidence:

- strict C11 warnings: PASS;
- ASan/UBSan with leak detection: PASS;
- Clang static analyzer: PASS;
- native shim coverage: 95.09% lines, 98.63% branches executed, 71.92% branch
  outcomes taken; the remaining outcomes are principally exhaustion/allocation
  and integer-saturation defenses that require explicit fault hooks;
- real llama.cpp shared-library build: PASS, 47 exported symbols;
- fixture behavior: PASS for interleaving, distinct buffers/context sizes,
  request bounds, atomic shrink refusal, stale handles, cancellation, pinned
  admission fallback, pinned limit refusal, busy unload, and final teardown;
- pure-Simple check: unavailable. The repository wrapper identifies itself as a
  Rust bootstrap seed and was not used. A separately recorded Stage-2 admitted
  artifact (`sha256:0e4aebc0569cfee5b455d5510b0c17301d376794b514300330639c8c07d0a2e5`)
  was probed in stage scope but lacks the `check` command, so it supplied no
  false verification claim.

This milestone does not claim simultaneous threads, paged attention/KV,
physical page sharing, copy-on-write tails, continuous batching, tiered spill,
or distributed cache transport.
