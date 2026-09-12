# Stage4 omitted core C runtime owners

**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

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

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule C: filed before 2026-07-29, no runnable repro in the record, no status line existed); closed as stale per the "too old / not valid -> close" triage policy. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification if reopened.
