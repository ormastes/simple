# Provisional Hello lacked first-build inventory initialization

Status: fix prepared; focused harness PASS; real candidate Hello pending.

The immutable Stage 2 candidate's fresh NTFS diagnostic Hello failed with
`SCV-E-ADMISSION: compile-event-journal-missing`. Evidence is retained at
`C:/dev/simple-phase4-provisional/provisional-v1/hello/compile.log`.
This is distinct from the earlier ReFS durable-flush stall.

`src/app/compiler_entrypoint/inventory_events.spl` requires explicit cold
initialization when no compile-event cursor exists. The provisional launcher
accepts a fresh source checkout but its Hello native-build did not request
initialization. The existing bootstrap SCV prime policy also limits cold
initialization to the first owner, avoiding a campaign-wide inherited flag.

`prepare-provisional-hello.shs` now selects cold initialization only when neither
`build/scv/source-inventory/CURRENT` nor legacy `build/scv/compile-events/CURRENT`
exists. Existing paths, including malformed publications or broken links,
select warm admission and remain subject to compiler validation. The flag is
scoped to the Hello compile and its value recorded in the hashed command
transcript. The compiler still computes and publishes the inventory through its
normal admission owner. No snapshot, receipt, runtime or source check is skipped.

The existing `provisional-hello-profile-test.shs` exercises the actual launcher
with a fixture producer that checks its received environment. On 2026-10-11 it
passed first-build initialization, inherited-cold override for an existing
malformed publication, retained legacy publication, argument transcript parity,
runtime drift rejection without a receipt, and real linked-runtime rejection.
Shell syntax and changed-file whitespace checks passed. These are harness
contracts, not compiler qualification or Phase 4 evidence.
