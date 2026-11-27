# Stage4 omitted core C runtime owners
## Open 2026-09-16 — needs owner triage

## Triage 2026-11-25

Still open; the header is accurate. The owner-resolution machinery the fix
section describes is present in the tree (requested-owner / pairwise-global
resolution in `src/compiler/70.backend/backend/llvm_native_link_orchestrator.spl`
and callers), but every "Remaining related blockers" item — the localized
projected capsule, the strict final link without duplicate-definition
suppression, candidate machine-header verification, partitioning the
remaining core C objects, and the SQLite/CLI capability owners — is
bootstrap-lane program work that cannot be advanced or verified on this
Windows host (no admitted self-hosted binary; `bin/simple.exe test` is
blocked repo-wide at HEAD by the known `@representation_boundary`
source/binary inconsistency). No execution evidence claimed; left open for
the bootstrap owner.

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## Symptom

Strict Stage4 inventoried the compiler capsule and five capability providers,
but it deleted them before calling the existing unique-owner resolver. Final
Simple objects request many symbols from the already-compiled core C objects,
so linking the six archives directly would leave missing owners and expose
unrequested globals. Windows also attempted to stage fork stubs as a provider.

## Fix and prevention

Pure-Simple now starts with the dependency-unblocking `runtime_native` object.
It derives and localizes that object's three legacy `spl_dl*` definitions so
the dedicated dynload archive remains the only global owner, verifies five
required string/time definitions, creates a deterministic one-member archive,
and adds it to pairwise-global and transitive `rt_*`/`spl_*` owner resolution.
Fork is included only on non-Windows hosts. The broader ten-object aggregate
was rejected during review because `runtime.c` and `runtime_native.c`
intentionally co-define globals; strict ownership must partition/localize those
objects before admission.

The path remains fail-closed after owner resolution. Direct archive linking is
still forbidden until selected archives are reduced to one exact projected
capsule with no unresolved runtime symbols. Focused source regressions pin the
legacy localization contract, hosted archive/object formats, one-member
composition, cleanup ordering, owner resolution, the retained projection
barrier, and the Windows fork exclusion.

No Simple, compiler, runtime, C, Cargo, or native execution is claimed under
this session's static-only restriction.

## Remaining related blockers

- Build one localized projected capsule instead of linking selected archives in
  declared order; the fork-to-memtrack cycle makes direct archive order unsafe.
- Disable duplicate-definition suppression and semantic-changing linker
  fallback for the eventual strict final link.
- Verify candidate machine headers before accepting x86-64, AArch64, or RISC-V
  artifacts.
- Partition/localize the remaining core C objects without relying on the normal
  linker's duplicate-definition suppression.
- Add the isolated SQLite and remaining CLI capability owners. Missing owners
  must continue to fail at requested-owner resolution.

