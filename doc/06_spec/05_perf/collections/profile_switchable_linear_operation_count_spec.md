# Profile-switchable linear lookup operation counts

**Requirement:** NFR-PSC-002. **Executable spec:** `test/05_perf/collections/profile_switchable_linear_operation_count_spec.spl`.

**Status:** Written, not executed on an admitted source-matched pure-Simple runtime. No performance PASS is claimed.

The spec forces linear storage separately for the text set, text map, generic map, and delegated generic set. At 32, 64, 128, and 256 entries, it checks that an empty miss makes zero equality checks, a hit on the last inserted key and a miss each make exactly `n`, and a hit on the first key makes one. It also checks membership, returned map values, and length so the counters cannot pass while the lookup result is wrong. Each counter is updated by the production lookup path and resets on each lookup.

The spec measures equality calls on linear lookups only. It does not measure insertion/removal comparisons, hash probes, ordered operations, allocation, copied bytes, RSS, warm latency, or target-profile behavior. These remain separate gates before NFR-PSC-002 or -005 can pass.
