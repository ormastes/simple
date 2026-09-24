---
id: link_native_cc_freebsd_obj0_only_2026-07-05
status: FIXED IN SOURCE — VERIFICATION PENDING
severity: medium
discovered: 2026-07-05
discovered_by: Code review of src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl
related: src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl
related: src/compiler/70.backend/linker/linking_process.spl
---

# Native linking: FreeBSD branch ignores runtime objects (uses only object_files[0])

## Summary

The FreeBSD native linking code path previously built link arguments from
`object_files[0]` only, dropping runtime objects and entry shim objects. The
source now routes the FreeBSD branch through `cc_fallback_object_args`, which
retains every object in the link.

## Evidence

- File: `src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl`
  (`os_name == "freebsd"` branch)
- The branch appends every result of `cc_fallback_object_args(object_files)`.
- `test/01_unit/compiler/linker/native_link_hardening_spec.spl` pins the
  all-object helper contract.
- A fresh native FreeBSD `--full` QEMU receipt remains pending; this source
  correction has not been claimed as live guest evidence.

## Impact

The old truncation could produce an undefined `_main` or runtime symbol on a
FreeBSD native build. The source correction removes that truncation.

## Scope

The FreeBSD branch now appends all fallback object arguments, ensuring runtime
objects and the entry shim are included in the final link.

## Next Steps

1. Run the focused host-safe linker contract spec.
2. Complete the separately owned fresh FreeBSD QEMU verification:
   `sh scripts/check/check-freebsd-bootstrap-qemu.shs --full`.
3. Record the guest identity and retained Stage 2/3 logs before claiming live
   FreeBSD link evidence.
