**Status:** open

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

## Handoff 2 (2026-10-23, lane A): all pool owners promoted; defect is cumulative-pool lifetime in the child

Landed and validated this round: decl pools (1b8136dd) then extend/pending
pools (b326b1b9) promoted across the transient scope. The 10 s repro
fingerprint (repro6) is unchanged in structure: a small text pool right
after the parser_state tail still carries a dangling element while its
siblings are valid, and desugar_module still SIGSEGVs.

Analysis at the limit of the workaround approach:
1. Every pool owner on the dump path is now promoted (par slots, 13 type
   pools, 44 decl pools, 13 extend/pending pools) and the promote chain
   reports parser_ok=true -- yet elements still dangle AT the capture
   dump, which runs while the parse scope is only PAUSED.
2. reset_all_pools clears ONLY the 56 types.spl pools. The decl/expr/
   stmt/extend/pending pools are NOT cleared between modules; the flat
   AST is cumulative per process with module boundaries tracked by slot
   counters (ast_decl_count_slot et al). A pool can therefore hold
   elements from an EARLIER module whose scope has ended, next to the
   current module's valid elements -- exactly the fingerprint (item0
   dangling, siblings valid; blob sizes far larger than p2_add alone).
3. Promoting a pool root only preserves the backing as of promote time;
   if the cumulative design expects per-module slices, the delegated
   child's extra scope boundaries reclaim slices the single-process
   design did not.

Conclusion: the fix belongs to the flat-pool owners -- either per-module
pool clearing before each parse/restore in the child, or a scope-lifetime
contract for cumulative pools. The sanitize/refusal/promotion workarounds
remain landed (they convert crashes into cache misses and removed three
crash layers) but cannot repair the module graph the consumer walks.
