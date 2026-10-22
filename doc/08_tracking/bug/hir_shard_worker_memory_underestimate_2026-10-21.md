# HIR shard admission underestimated the producer footprint

Status: source candidate; runtime qualification pending. Base source: `55ba9dc6dbea8db49a81dfc7fdc9274efc68a8df`.

The retained Phase 3 attempt-one guard recorded 67,200,120 KiB against its strict 67,108,864 KiB tree cap, exited 88, and became quiescent. This is an observed resource-cap failure, without a host OOM or language-failure claim. The source candidate and running producer were different immutable identities; this patch cannot change that already-running binary.

Phase attribution matters: `build.log` reports all 20 parse warmers completed before admitting 13 HIR workers using the 3,000,000 KiB estimate. Sparse snapshots of those HIR processes reached 4,212,404 KiB per worker; the parent reached 6,522,576 KiB. These are sampled observations, not exact per-worker high-water marks. They do not disprove the separate parse-warmer estimate.

The candidate samples the existing canonical process high-water-mark facade once at HIR admission, after parse preparation. The default HIR estimate becomes the maximum of its existing phase default, host hint, and parent peak. A valid explicit `SIMPLE_HIR_SHARD_WORKER_KB` remains a deliberate override. No universal large constant or new probing mechanism is introduced. Serial HIR admission now executes the existing bounded host/cgroup probes that the prior early return skipped; small-project startup overhead requires measurement.

For a known effective tree cap, the pool reserves the larger of the existing 40% reserve and parent peak, then admits at most the remaining bytes divided by the worker estimate. Arithmetic divides before multiplying and subtracts only after bounds checks. A serial HIR request is checked too; zero-fit admission skips HIR warming instead of reviving an isolated worker. This does not admit or reject the subsequent final compiler worker.

The failed fixture with a 6,522,576 KiB parent estimate admits six HIR workers instead of thirteen. Small parent footprints preserve the existing default. Parse and MIR policy remains unchanged. Host maximum threads, cgroup/tree bounds, and the host-clamp opt-out retain their existing precedence; disabling host estimation cannot disable a known tree cap.

The parent peak is a workload-sensitive heuristic, not a bound on future child growth. An unavailable provider falls back to the phase estimate with an explicit diagnostic. The strict RSS watchdog remains authoritative, and may reject a build despite this estimate. Existing parent scratch reclamation may make its peak conservative; elapsed time and peak memory still require paired measurement before any performance claim.

## Queued qualification

The single build owner must run the changed unit specs on a qualified full CLI, then the repository compiler/lib/MCP checks and runtime/native smokes required by AGENTS.md. Verify exact fit, one-under, serial no-fit, overflow, invalid overrides, host/environment caps, small versus large workloads, HIR routing, and final-worker behavior. Run the same representative workload with immutable before/after producer identities, unchanged strict guard, and separate small/large rows for elapsed time and peak tree RSS. No new build or benchmark was started by this lane.

Executable regressions: `test/01_unit/app/cli/shard_mem_clamp_spec.spl` and `native_build_shard_admission_spec.spl` in the same directory. Static checks are distinct from executable acceptance; no production readiness PASS is claimed.
