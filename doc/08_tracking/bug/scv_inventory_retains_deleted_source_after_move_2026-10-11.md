# SCV source inventory retains deleted path after module move

Status: MITIGATED for the focused Stage 2 build by explicit cold inventory rebuild (2026-10-11). Current-source V4 warm behavior remains unverified.

In the isolated worktree at c7c4db75056833a5112395c0b762c54c5a154b5c,
src/compiler/70.backend/linker/linker_lifecycle.spl and linker_pack.spl
became compatibility facades. Their implementation moved to
src/plugins/linker_pack/lifecycle.spl and session.spl. The intermediate
src/os/smf/linker_lifecycle.spl path is absent and is not tracked by Git.

A no-stub pure-Simple Stage 2 native-build using --entry-closure and all
src/compiler, src/lib, src/os, src/plugins, and fixture roots fails before
parsing with:

    SCV-E-ADMISSION: snapshot-read-failed:src/os/smf/linker_lifecycle.spl

The failure repeats after committing the move.
build/scv/source-inventory/CURRENT reports the new git_head but
filesystem_rows=0; its selected generation has 45,446 rows and still
contains both the removed OS path and the new plugin path. The active
generation digest stayed b88e2d1a004ea4e2976919461d4c9ab37915a8e6acb640fc95cdbebbb76e0e1d.
Git ls-files confirms the old OS path is absent and the new plugin path
is tracked. The inventory must invalidate removed tracked source identities
when HEAD or source roots change.

Reproduction log: build/mini_builds/item5_linker_pack_plugin_owner_committed_native.log.
Expected: the deleted OS path is removed from the selected source inventory,
the new plugin path is selected, and snapshot admission reaches parse.
Do not treat this error as evidence that the plugin owner compiled.

## Follow-up evidence (2026-10-11)

The producing Stage 2 binary persisted a V3 cursor. The current source in
src/app/compiler_entrypoint/inventory_events.spl uses a V4 tracked-path
membership record; its warm route refuses a cursor without that record and
directs the caller to SIMPLE_SCV_INVENTORY_COLD_INIT=1. The older V3
producer had no tracked-path deletion record for the staged intermediate
OS path, so advancing HEAD alone could not remove it.

One bounded retry with SIMPLE_SCV_INVENTORY_COLD_INIT=1 rebuilt the inventory
from Git. The selected generation no longer contains the removed OS path
and includes src/plugins/linker_pack/lifecycle.spl. Snapshot admission
then passed; source closure selected 577 modules and HIR completed 577/577.
The 600-second wrapper timed out later and its worker exited without an
executable. Log: build/mini_builds/item5_linker_pack_plugin_owner_cold_native.log.

The next validation should use a current-source V4 producer and prove
staged intermediate path removal on warm refresh without cold init. The
native fixture also needs a separate completed build and runtime result.

## Current-source V4 regression attempt (2026-10-11)

`test/fixtures/compiler/target6_tracked_move_refresh_probe.spl` now models
the exact staged intermediate path: admit the original, stage and admit the
OS path, remove it before committing the final plugin path, then warm refresh.
The fixture checks that only the final path remains and repeats the warm read.
It had **not** executed at that point. Its initial bounded no-stub Stage 2 native build
compiled 66 selected modules but failed while linking two undefined globals
from `compile_source_inventory_core.spl`. See
`scv_native_reexported_constants_undefined_2026-10-11.md`.

The production bridge now imports focused `app.io` directory, file, and
process facades instead of the broad `app.io.mod` hub. With the same source
roots, the selected closure fell from 110 to 66 modules; this is a closure
count, not a measured startup, p95, or RSS result. The previous broad-closure
build failed at MIR in unrelated environment and SDN modules. This regression
still needs an executable native PASS after the linker and runtime blockers
are repaired.

## Native runtime follow-up (2026-10-11)

Making the two SCV core constants public resolved the native link. The first
executable attempt exposed an omitted `-c` in the fixture's Git commit
arguments; correcting it reached the cold refresh, where a typed `None`
entered an `if trace != nil` branch and `trace!` panicked. GDB and object
disassembly identify that separate compiler/runtime equality defect in
`native_typed_option_none_not_equal_nil_2026-10-11.md`. The bridge now guards
its optional trace with `trace.?`.

The third bounded build linked, but the fixture exited 139 during its first
cold refresh (`timeout: the monitored command dumped core`). Its temporary
Git repository has the seed commit, and the SCV cache contains only
`compile-events/refresh.lock`; no inventory generation or cursor was
published. No core file or `coredumpctl` was available on this host. The
three-cycle fixture limit is reached for this session. This is **not** a V4
warm deletion PASS or Item 6 cutover evidence. The next session needs a
captured native crash stack from a repaired candidate before another warm
refresh claim.

## Later native cold-refresh diagnostic (2026-10-11)

Three further bounded no-stub builds linked the 66-module fixture, but each
executable failed before cold publication with an invalid array handle and
`cold-init-listed-no-sources`. The temporary Git repository did contain the
tracked source. Optional-trace and Git-listing return rewrites did not change
the result and were removed. A focused process-output ABI probe is authored
but unexecuted; see
`doc/09_report/compiler/target6_tracked_move_native_abi_diagnostic_2026-10-11.md`.

The focused 44-module process-output fixture later passed the exact cold
`ls-files` request and text split. An explicit-validity Git-event batch
candidate linked in the 66-module fixture, which then crashed in
`CompilerInventoryTraceV1.captured_pointer` before publication. The next
bounded run must resolve that trace boundary and still prove the full V4
tracked-move sequence; the direct Git output test does not prove it.

GDB later identified the exact cold source-path loss in the Stage 2 native
fixture: `line[2:]` produced a 32-byte `.sp` path from Git's 33-byte `.spl`
row, so the path validator filtered it. The bridge's four open-tail text
slices now use `substring(start)`, but that candidate has not been rebuilt
after the three-cycle cap. See
`native_text_open_tail_slice_truncates_final_byte_2026-10-11.md`.

The next three 66-module native builds linked. The open-tail repair reached
membership publication; byte hashing fixed a malformed native digest path;
exclusive creation plus readback advanced past the known native atomic-write
failure. The fixture now stops at `observed-event-apply:event-entry-invalid`,
with GDB showing event `byte_count=-1`. See the updated native ABI diagnostic
and `native_scv_event_content_length_invalid_2026-10-11.md`. No cold or warm
inventory generation has passed, so this bug remains OPEN.
