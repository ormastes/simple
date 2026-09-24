<!-- codex-design -->
# Slang KV cache optimization requirements

Date: 2026-09-09
Selection: Feature option B.

- **REQ-001:** Measure snapshot and physical KV generation through matched,
  explicitly identified model, tokenizer, CPU, thread, context, sampler, batch,
  KV dtype, flash-attention, and KQV-offload settings.
- **REQ-002:** Record cold, exact-repeat, alternating-prefix, eviction, and
  prefix-extension workloads separately.
- **REQ-003:** Report actual generated tokens, prompt tokens reused, prompt
  tokens prefetched, committed prefix restores, boundary evaluations, copied
  tail rows, failures, physical bytes, and ownership cleanup.
- **REQ-004:** Physical generation must find the longest exact-token prefix,
  reuse sealed full pages, copy a partial tail when required, evaluate only the
  uncached suffix, and publish changes transactionally.
- **REQ-005:** Prefix extension must retain exact token validation, execution
  namespace isolation, copy-on-write ownership, and fail-closed fallback.
- **REQ-006:** Engine cache statistics must report the active execution mode and
  must not present snapshot counters as physical-provider observations.

No UI is introduced.
