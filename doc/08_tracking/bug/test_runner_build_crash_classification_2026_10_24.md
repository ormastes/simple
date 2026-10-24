# Annotation: test_runner_build crash classification, three workaround classes exhausted (2026-10-24, lane D)

Addendum to `hir_shard_sigbus_crash_attribution_20261024.md` and
`windows_phase34_open_verification_inventory_2026_10_24.md`. Classifies the
stage2 test-matrix `test_runner_build` row (native-build of
`src/app/test_runner_new/main.spl` by the admitted stage2 candidate,
x86_64-pc-windows-msvc) after three distinct workaround classes all failed.

## Evidence

1. **Matrix context (verifier env):** the row publishes its HIR shard
   inventory, then a worker dies with 0xC0000005 in HIR/lowering work
   (~50/287 modules, ~140 s in). 3/3 fresh attempts. The verifier then records
   the row CRASH and the remaining rows degrade (MIR shard inventory-refusal,
   in-process fallback idles on the shared cache).
2. **Standalone replay, fresh cache, verifier policy env:** the HIR shard
   inventory publish is REFUSED ("HIR inventory/cache unavailable" -> MIR
   fallback -> in-process fallback) -- the standalone env lacks whatever the
   verifier supplies for the inventory publish. The in-process fallback then
   CRASHES with the same 0xC0000005 (RC=139, post-lowering/post-store counters
   0 errors immediately before the AV). Conclusion: the crash follows the
   lowering work in ANY execution path (shard worker or in-process fallback);
   there is no path-around.
3. **cdb scripted catch** (multi-g command file, 500 s budget, fresh cache):
   NO access violation under the debugger (RC=124 timeout) -- this
   manifestation is debugger-prevented (heap-layout perturbation), like the
   baseline frontend refusal. The catch recipe cannot name this site.
4. **Cache-resume retry loops cannot cross the crash:** a crashed run's HIR
   cache is left mid-write; the next run's shard inventory publish fails with
   "cache unavailable" (verified with reused caches in both the matrix loop
   and standalone). Only fresh caches publish inventory, and fresh caches
   re-crash (class 1).

## Conclusion

`test_runner_build` is blocked by the heap-corruption defect itself, in its
lowering/mono phase. The three cheap workaround classes (heap-luck retry,
debugger catch, cache-resume loop) are each refuted by a dedicated experiment.
The row -- and therefore the stage2 test-matrix gate and the managed Phase
3/4 resume -- needs the defect fixed at source. The retained stage2 receipts
and the `--resume-managed-from-admitted` path in the lane-64 storage remain
valid for an immediate resume once a candidate built on a fixed base is
admitted.
