# macOS Stage 4 memory sampler used Linux-only /proc

Status: SOURCE FIX DRAFTED; executable Stage 4 evidence pending.

`scripts/check/check-stage4-memory-gate.shs` invokes `src/app/memstat/main.spl`,
which previously required `/proc/<pid>/stat` and `/proc/<pid>/smaps_rollup`.
Neither path exists on macOS, so the gate could not measure RSS on the Apple
Silicon bootstrap host. This left the Stage 4 memory limit without a local
sampler while the full CLI build was blocked upstream.

The sampler now queries `ps -p <pid> -o rss=` once per interval on macOS and
keeps the existing CSV schema. Linux-only PSS, dirty-page, swap, and fault
columns contain `-1` on macOS. A vanished PID ends sampling. The system spec
checks positive RSS and the unavailable-column sentinel on macOS.

The direct `ps` process call avoids shell interpolation and the existing
process monitor's multiple `ps`/`lsof` calls per sample. This is a sampling
overhead improvement, not proof that the compiler itself uses less memory.

Acceptance remains open: run the spec and gate with a source-matched pure-Simple
full CLI, then measure a current macOS Stage 4 build's peak RSS and elapsed
time. The local host has under 8 GiB free, below bootstrap's 20 GiB preflight
floor; current main's macOS Phase 2/3 CI had no job when this source fix was
prepared.
