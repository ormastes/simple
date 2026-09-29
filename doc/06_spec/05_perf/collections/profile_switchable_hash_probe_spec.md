# Profile-switchable hash probe counts

**Requirements:** NFR-PSC-002 and NFR-PSC-003. **Executable spec:** `test/05_perf/collections/profile_switchable_hash_probe_spec.spl`.

**Status:** Written, not executed on an admitted source-matched pure-Simple runtime. No performance PASS is claimed.

At 32, 64, 128, and 256 entries, the spec forces hash storage in the text set, text map, generic map, and delegated generic set. Each container receives a distinct `ast://` site and runs `n` successful plus `n` unsuccessful lookups. The spec checks results and verifies the captured per-site `lookup_count` is exactly `2n`, the probe total lies from `2n` through `16n`, and collisions do not exceed probes. The upper bound is a fixture-specific scaling guard for these keys; it is not a deterministic worst-case guarantee for hash tables.

The metric rows come from the existing bounded execution-owned capture path. This spec does not measure insertion/removal probes, allocations, copied bytes, RSS, warm latency, or adversarial collision distributions. Robust and critical policies must continue to reject unbounded hash selection independently of these measurements.
