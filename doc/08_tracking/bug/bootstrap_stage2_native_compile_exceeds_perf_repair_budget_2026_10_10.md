# Stage 2 native compile exceeds the performance-repair budget

Status: OPEN; this is a measured stopping point, not a proven regression against a paired compiler baseline.

On source base `6bd7701ad65705884478aad3629cb2373d10342b` plus the owned incremental/SCV and bootstrap scheduling patches, the repaired full bootstrap passed all five preflight checks in 56 seconds, then Stage 2 native compilation consumed the remainder of the 600-second overall diagnostic budget. The watchdog exited 124 after 601.37 seconds, reported aggregate tree peak 2,271,552 KiB (cap 5,859,375 KiB), and confirmed quiescent=1. No Stage 2 executable or admission was produced; Stage 3 and normal self-hosted tooling therefore remain unavailable in this lane.

Retained evidence: `build/native_probe/current-release-bootstrap/perf-fix1/{bootstrap.log,rss.env,time.txt}` and `build/bootstrap-phase23/logs/aarch64-unknown-linux-gnu/stage2-native-build.log`. Rust authority/dependency and native caches remain in place. The log contains accepted seed aggregate return-type warnings; they do not identify the expensive phase or prove the timeout's cause.

Next investigation should isolate native compile subphases using existing cache and canonical authority, distinguish type/mono lowering from backend/link time, and qualify the resulting pure-Simple compiler before comparing Phase 2/Phase 3 speed on a matching fixture. Do not infer a compiler speedup from the separate Cargo cache-routing fixture.

Related repair and measured fixture: [preflight cache repair](../../09_report/compiler/bootstrap_preflight_cargo_cache_perf_fix_2026-10-10.md).
