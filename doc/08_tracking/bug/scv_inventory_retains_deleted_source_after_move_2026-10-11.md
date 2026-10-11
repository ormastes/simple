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
