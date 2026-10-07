# Compiled bootstrap parse shards dispatch to the generic native-build owner

Status: source repaired; selected contract validation and native parse-cache qualification recorded separately.

The bootstrap internal entry allowlist accepts parse_shard_main.spl and native_build_worker.spl, but previously dispatched both to cli_native_build_with_environment_variant_policy_v1. A marked parse child bypassed its slim owner, including heartbeat, parse-only startup, inherited closure-request validation and driver_run_parse_shard. Cold Cranelift whole-compiler bootstrap normal route reached aggregate 6GiB before HIR, while concurrent children walked large closures and no parse-shard heartbeat appeared.

Repair: expose the unchanged parse-shard body as run_parse_shard(args), retaining worker marker, authentic typed policy handoff, source-root/closure/snapshot authority validation, shard cache ownership and parse-only exit. Bootstrap now selects this owner before backend registration. Native-build worker route retains backend registration and generic native-build policy handoff unchanged. Internal route selection has a tiny dependency-free owner so its policy contract does not import an entire compiler while being tested.

Preserved first failures: private full-bootstrap contract test exceeded2GiB (exit88). Standalone slim worker entered the owner with an authentic policy handoff then the bootstrap seed interpreter rejected valid ModuleSurfacesByName.empty() as unknown class. No parsed-cache output or native PASS claimed from that failing probe; this valid source-form issue needs independent interpreter owner qualification. No syntax workaround or memory-cap relaxation was made.

Production compilation must run actual marked parse-shard positive and forged/mismatched closure negative probes on the rebuilt native producer, preserving cold-cache scope and serialized parse outputs. Real native qualification remains pending; policy tests alone cannot prove reduced RSS.
