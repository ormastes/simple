# Target 5 C backend partition cleanup (2026-09-29)

The compiler's duplicate `CCodegenAdapter` had no source caller; the backend
registry already imports `plugins.backend_c.c_codegen_adapter`. It was removed
with its compiler facade exports and obsolete closure-manifest exception.
The standalone C compile entry was moved unchanged from
`src/compiler/70.backend/backend/compile_c_entry.spl` to
`src/plugins/backend_c/compile_c_entry.spl`. Its source-shape tests, static
SFFI authority guard, and path-based ratchet records now follow that owner.
The bootstrap portability assertion for HIR provenance was updated to its
existing `retained_module_surfaces` call, since its former `{}` expectation
was stale.

The widened kernel closure audit moved from 3 K0-to-P, 13 K1-to-P, and 9
kernel-to-app/OS violations to 3, 9, and 9. It still fails. The focused
`backend-compile-c-sffi-authority.shs` guard passes. The broader bootstrap
portability script stops at an unrelated `policy-derived backend help missing`
check before completing. The raw-SFFI, fail-open, and use-target ratchets
also fail with large tree-wide new/stale baseline sets; they do not qualify
this change. No Stage4 binary size, startup, or runtime behavior is claimed.
