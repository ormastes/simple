# Release tag builds fail SCV admission: `git-event-apply:event-invalid`

- **ID:** `release_scv_cold_init_event_invalid_non_source_paths_2026-09-16`
- **Status:** FIXED (producer-side source-path filter + quotePath fix, PR
  bundled with the 1.0.0-beta.6 release; cold-walk wall-time reduction
  remeasurement still open — see
  `windows_scv_inventory_cold_init_untracked_walk_slow_2026-09-13`)
- **Area:** `src/app/compiler_entrypoint/inventory_events.spl`
  (`compiler_inventory_event_push_v1`, cold-init `ls-files`),
  `src/lib/scv/compile_source_inventory.spl`
  (`compile_source_inventory_apply_filesystem_events_v1`)

## Symptom

Every legacy release.yml native-build leg (linux-x86_64, windows-x86_64)
failed at the end of a ~1.7 h build with:

```
SCV-E-ADMISSION: git-event-apply:event-invalid
```

(first observed on release run 35029559718, tag v1.0.0-beta.5; beta.4 runs
had died earlier — windows on OOM, linux on infra-cancel — before reaching
the admission verdict, so the gate had never produced a green release leg
since it was added on 2026-09-13).

## Root cause

Cold init (`SIMPLE_SCV_INVENTORY_COLD_INIT=1`, sanctioned opt-in for fresh
checkouts) lists **every** file under `src/` via
`git ls-files --cached --others --exclude-standard -- src` and turns each
into a `git` event with no extension filter. `src/` holds ~60k files, ~44k
of them not Simple source. `compile_source_inventory_apply_event_v1` admits
only `.spl` / `simple.sdn` paths (`path_valid_v1`), so the first listed
non-source file (`src/FILE.md`) rejected the whole batch with
`event-invalid`. Any fresh checkout — branch or detached tag — hit this;
release.yml is simply the workflow that runs the seed's native-build
directly on a cold checkout and release-blocks on the verdict.

Secondary latent bug: the cold-init `ls-files` lacked
`-c core.quotePath=false` (the incremental `diff`/`ls-files` calls already
set it), so paths with non-ASCII bytes would arrive C-quoted (`\`, `"`) and
also fail `path_valid_v1`.

A second producer had the same hole: the filesystem-watch translator
(`apply_filesystem_events_v1`) pushed every watched path, so one editor
saving a non-source file could fail the whole refresh batch.

## Fix

- `compiler_inventory_event_push_v1`: skip paths failing
  `compile_source_inventory_path_valid_v1` before any file read — fixes
  admission and also avoids hashing the ~44k non-source files during cold
  init (the remaining cold-walk cost reduction is tracked in the 09-13 bug
  above).
- Cold-init `ls-files`: add `-c core.quotePath=false`.
- `apply_filesystem_events_v1`: skip non-source identities (`continue`).
- `apply_event_v1` intentionally left strict — producers now guarantee the
  inventory only ever contains compilable source paths.

## Regression tests

`test/01_unit/lib/scv/compile_source_inventory_spec.spl`: two content-ratchet
`it` blocks pinning the producer filter and the quotePath flag.

## Host-environment classification (2026-09-18)

Audited by the fix-pipeline classification review: **environment-blocked: windows** — [env-blocked:windows]. This row is not executable on the macOS aarch64 host fix lane; it resumes when the blocking condition clears.
