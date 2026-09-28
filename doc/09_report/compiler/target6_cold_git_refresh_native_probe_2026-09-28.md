# Target 6 cold and warm Git-event native probe (2026-09-28)

The isolated `codex/target56-next` worktree at source revision
`755813dc101c347d7cdfb1e45b920da95ab25aa0` built
`test/fixtures/compiler/target6_cold_git_refresh_probe.spl` with the
admitted Stage2 pure-Simple compiler
`d57b8ff1c676c0e250f76f713a5e8e5b0bbf3d91fd72741698e8fe0f26ad033c`.
The native probe binary has SHA-256
`f8e4ca8ebadfbe3608976ca49cd7e5d1f80231b69d71c3f67025f1c84e0fd715`.
The build set `SIMPLE_NO_STUB_FALLBACK=1` and
`SIMPLE_SCV_FREEZE_FALLBACK=1`, used `--entry-closure`, compiled 83 source
units, and linked through the core-C runtime. The final rebuild reused 82 of
83 units. Logs and binary are under
`build/mini_builds/target56_cold_git_refresh_probe/`.

The probe creates its own one-file committed Git repository and calls the
production `compiler_inventory_refresh_v1` bridge. It checks a cold inventory
with exactly `src/a.spl`, an unchanged warm refresh with the same digest, a
warm tracked edit with a changed content digest, and a warm tracked deletion
with zero remaining entries. The native run exited 0 and printed
`PASS target6_cold_git_refresh_probe`. The bridge passes every cursor argument
explicitly to `compile_source_inventory_apply_observed_events_v1`.

This clears the historical `observed-event-apply:event-invalid` failure for
this exact tiny source and binary combination. It does not inspect a larger
Git batch, qualify filesystem-journal races or untracked membership changes,
prove the full typed index publication, or provide a Target 6 SPipe/performance
cohort. A current-source Stage4 compiler and the production fixture remain
required for final admission.

Follow-up: the current-source V3 probe now also passes warm untracked
create/delete under the same no-stub, entry-closure Stage2 method. See
`doc/09_report/compiler/target56_entry_closure_native_followup_2026-09-28.md`.
