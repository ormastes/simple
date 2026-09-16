# System-test source aliases are dangling and duplicate driver embedding

## Status

Claimed and fixed 2026-08-12.

## Defect

The source aliases copied from `test/feature/lib` into the one-level-deeper
`test/03_system/feature/lib` retained their old `../../../src/*` targets.
Those targets resolve beneath nonexistent `test/src`, so the Rust driver's
follow-links test discovery silently omitted the canonical aliases.

Changing only the link depth would expose the same physical source-adjacent
specs through both legacy and canonical aliases. `driver/build.rs` previously
generated a distinct Rust wrapper for every logical alias, duplicating work.

## Fix and regression

The three canonical links now target `../../../../src/{app,compiler,lib}`.
Driver discovery sorts logical paths and admits the first path for each
canonical physical file, making wrapper selection deterministic and unique.
`driver/tests/build_script_symlink_dedup.rs` checks the exact three link
targets/resolutions and an adjacent two-alias fixture that must yield one
canonical wrapper.
