---
id: link_native_cc_freebsd_obj0_only_2026-07-05
status: OPEN
severity: medium
discovered: 2026-07-05
discovered_by: Code review of src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl
related: src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl
related: src/compiler/70.backend/linker/linking_process.spl
---

# Native linking: FreeBSD branch ignores runtime objects (uses only object_files[0])

## Summary

The FreeBSD native linking code path in `src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl` (around line 580) builds link arguments from `object_files[0]` only, dropping runtime objects and entry shim objects. The macOS branch (lines 556-573) was recently fixed to include all objects in the link, but the FreeBSD branch remains defective and will produce an undefined `_main` symbol error on FreeBSD native builds.

## Evidence

- File: `src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl` line 580
- macOS branch: correctly iterates `for obj in object_files` (lines 556-573)
- FreeBSD branch: accesses `object_files[0]` directly, ignoring other objects
- Pattern: Same defect fixed in macOS branch but not backported to FreeBSD
- Unverified on actual FreeBSD (no host available for testing)

## Impact

Native linking on FreeBSD will fail with undefined `_main` symbol or other runtime symbols, preventing successful binary link. The defect is identical to the recently-fixed macOS issue, so a straightforward backport of the macOS loop structure will resolve it.

## Scope

The fix is mechanical: replace the FreeBSD branch's `object_files[0]` access with the same `for obj in object_files` loop pattern used in the macOS branch. This ensures runtime objects and entry shim are included in the final link.

## Next Steps

1. Mirror the macOS all-objects loop (lines 556-573) into the FreeBSD branch.
2. Test the fix on a FreeBSD host or via the automated QEMU bootstrap check (`scripts/check/check-freebsd-bootstrap-qemu.shs --smoke`).
3. Verify that `_main` and runtime symbols resolve correctly in the linked binary.
