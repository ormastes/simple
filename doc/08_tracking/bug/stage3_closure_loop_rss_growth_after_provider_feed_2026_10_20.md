# Stage 3 closure loop: RSS grows 20-36 MB per module with the provider feed (release_phase3)

- Status: OPEN
- Date: 2026-10-20
- Platform: aarch64-unknown-linux-gnu
- Severity: P1 (Stage 3 tree cap 52 GiB is nearly exhausted by the closure loop)

## Observation

Stage 3 resumed from bootstrap-r16b (release_phase3 f9527544c50 + the
rt_process_rss_kib capsule fix; Stage 2 sha256 645e62a815d0...), DIRECT
route (SIMPLE_NATIVE_BUILD_THREADS=1), closure 1352 modules. Closure-loop
lowering runs with the transient scope (#3919) and the provider feed (#3938):

- HIR complete: RSS 6.6 GB (heap_live 2.34 GB).
- after ~1123 closure modules (2 h): RSS 46.6 GB, i.e. ~36 MB/module on
  average; sampled rate at that point ~20 MB/module (+352 MB over 18
  modules).
- throughput 18.4 modules/min (r8 base without the provider-walk perf chain:
  4.7/min; heap +8.2 MB/module, RSS +28 MB/module).

Projected end of closure loop: ~51 GB against the 52 GiB tree cap, leaving
little room for entry lowering and codegen. The memory-snapshot file only
covers HIR, so heap vs RSS in MIR is not split here; the r8-base run's
`SIMPLE_MIR_SECTION_PROFILE_FILE` showed heap +8 MB/module vs RSS
+28 MB/module, i.e. most of the growth was not live heap.

## Next step

Run the closure loop with `SIMPLE_MIR_SECTION_PROFILE_FILE` (heap_live and
rss per `s4_promote_*` mark) on this tree to split retained heap from
allocator retention, then find which per-module provider registration
products survive the transient scope.
