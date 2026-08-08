# Stage4 omitted core C runtime owners

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

After owner resolution, Pure-Simple now partial-links only the selected exact
archives, forces the original requested roots, localizes every other global,
rejects unresolved runtime symbols and constructor sections, and rescans a
deterministic one-member capsule before strict final linking. Strict linking
admits only user objects, the entry object, and that capsule; duplicate-symbol
forgiveness and direct-link fallback are disabled. Focused source regressions
pin root-versus-transitive localization, cycle-safe Linux grouping, Mach-O root
forcing, cleanup ordering, owner resolution, and the Windows fork exclusion.

No Simple, compiler, runtime, C, Cargo, or native execution is claimed under
this session's static-only restriction.

## Remaining related blockers

- Verify candidate machine headers before accepting x86-64, AArch64, or RISC-V
  artifacts.
- Partition/localize the remaining core C objects without relying on the normal
  linker's duplicate-definition suppression.
- Add the isolated SQLite and remaining CLI capability owners. Missing owners
  must continue to fail at requested-owner resolution.
- Run the focused projection, strict native-link, and full Stage4 executable
  checks when the active execution restriction is lifted.
