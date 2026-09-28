# Target 5/6 focused entry-closure native follow-up (2026-09-28)

The two earlier V2 index probe builds that reached about 40 GiB RSS omitted
`--entry-closure`. The retained successful native Git probe used it. Repeating
the current V2 compare-and-publish probe with that flag and
`SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_SCV_FREEZE_FALLBACK=1` built with the same
admitted pure-Simple Stage2 compiler SHA-256
`d57b8ff1c676c0e250f76f713a5e8e5b0bbf3d91fd72741698e8fe0f26ad033c`.
It compiled two units, reused 26 cached units, linked in 1.85 wall seconds at
137,872 KiB peak RSS, and printed `PASS package_index_publish_cas_native_probe`.
The 140 KB binary SHA-256 is
`c105a110cbbca6bd00131f0fea8bc0d3036a2d34f91949c2b7f62d0a29204e9c`.
The build log and binary are under `build/mini_builds/target56_index_v2_cas_closure_*`.
The final V2 package-index, warm-route, and cold-builder SPipe unit files also
reported 3/3, 5/5, and 6/6 through the bootstrap interpreter. These focused
checks cover V2 encoding, variant-bound action identity, empty/cross-variant
route rejection, and the graph builder; they do not publish a production graph.

The current-source V3 Git bridge probe compiled 83 units with no cache reuse
under the same no-stub, entry-closure, core-C path. It built in 3.01 wall
seconds at 327,664 KiB peak RSS and printed
`PASS target6_cold_git_refresh_probe`. The 245 KB binary SHA-256 is
`afa964225f6fe8356e35c7023309edcf69be9332af56f0a6d1384f50c0cd329a`.
Its fixture checks cold, unchanged warm, tracked edit/delete, and untracked
create/delete refreshes in a committed one-source Git repository. The
`inventory_events.spl`, `compile_source_inventory.spl`, and fixture source
SHA-256 values are respectively
`80f32c6e2f119efff2b1ea5bf9510fdff3fbc34245c685a094c2f22c1a9c1d18`,
`09feb2f78de8869e1f8e90f5b2ae297c471642d79739520ab4ce1a9b6cec25bf`,
and `f6d5938765995ce2ffc34bc67039944b0f52c3c775f878d42cdf0c63e9144545`.
Logs and binary are under `build/mini_builds/target56_cold_git_refresh_probe/`.

The entry-closure flag resolves the focused-build memory blocker. It does not
prove that broad source-root native builds are memory-safe: those invocations
remain open in the tracking bug. Neither probe is the Stage4 full CLI, a
production-size repository, or a 30-sample time/RSS cohort. Target 5's
release-small binary-size and startup gates and Target 6's production graph
publisher, full entrypoint cutover, and performance gate remain open.
