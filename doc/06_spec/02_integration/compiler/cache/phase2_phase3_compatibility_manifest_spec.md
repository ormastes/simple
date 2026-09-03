# M3 Phase 2 to Phase 3 Compatibility Manifest

- Executable: `test/02_integration/compiler/cache/phase2_phase3_compatibility_manifest_spec.spl`
- Requirements: `MBH-REQ-003`, `MBH-REQ-004`, `MBH-REQ-005`, `MBH-REQ-006`, `MBH-REQ-009`
- Evidence class: executable SPipe definition; no execution result is embedded.

## Scenarios

- should keep writable caches separate and treat Phase 2 as read-only
- should reuse producer-neutral frontend values with attribution
- should reuse only exact compatible native objects with attribution
- should reject corruption and wrong producer provider target or schema
- should reject mutated M2 receipt authority and stale key generations
- should compare normalized clean and reused output bytes
- should canonically decode and reject corruption or trailing bytes
- should consume only the current admitted M2 frontend projection
- should reject filesystem aliases symlinks and prefix collisions
- should reject manifest symlink and canonical aliases through the production reader
- should leave no final object when publication is interrupted before commit
- should compare normalized clean and reused output artifacts

## Freshness

The requirement IDs and scenario titles mirror the executable source. No
runtime or native PASS is claimed.
