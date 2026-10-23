
## Handoff 2026-10-23 (lane A): workaround stack at its limit; corrupt module born in the child parse

Three fixes landed and validated incrementally (each removed one crash
layer):
1. 5b076f56 sanitize-refuse-capture: store-side rt_panic -> poisoned blob
   discarded, cache store skipped. VALIDATED (refusal prints, no panic).
2. e27c0c66 decode-refusal: restore dry-run validation; dangling pools
   refuse the hit -> reparse. VALIDATED (refusal fires).
3. 2b73873a dry-run uses dump_all (dump_for_cache opens a nested transient
   scope and panicked). VALIDATED (refusal fires 3x per sanity run).

Remaining failure (lane A run k): `[flat-pool] capture refused ...` x3,
then SIGSEGV in `compiler__frontend__desugar__desugar_module` (signal 11,
.ips 111909). KEY INFERENCE: the capture refusal now fires on FRESH
child parses too -- with the cache fully off (SIMPLE_FRONTEND_CACHE=0) the
build does not crash only because no capture encode runs at all (it dies
later at an unrelated MIR repository-policy check in the minimal repro
env). So a pool text dangles by capture time in the DELEGATED CHILD's own
parse, independent of decode. Refusing store/decode cannot clean the
module; the consumer (desugar) still walks the dangling text.

The defect is therefore in the child's parse/scope lifetime: a pool text
allocated in a scope that ends before the capture dump / module
consumption. This needs the scope-owner fix (the reset_all_pools counter
trace data exists under SIMPLE_POOLDBG=1; the discriminating next probe is
a pool-element liveness check at scope pause vs end in the child).
Lane A stops here per the cycle cap -- over to the flat-pool owner lane
with the full evidence chain.
