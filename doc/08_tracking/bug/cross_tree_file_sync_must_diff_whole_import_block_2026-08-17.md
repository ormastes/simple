# Cross-tree file sync must diff the whole import block, not just the synced function

- **Date:** 2026-08-17
- **Status:** OPEN (process defect; the concrete instance is fixed)
- **Found by:** bootstrap cycle 4b, `simple-boot-snap`

## Symptom

Stage 2 of `bootstrap-from-scratch.sh` failed at LINK, not at compile:

```
/usr/bin/ld: .../mod_602.o: in function
  `compiler__driver__driver_hir_pipeline_lowering__CompilerDriver.lower_and_check_impl':
compiler__driver__driver_hir_pipeline_lowering:(.text.simple.9+0x3047):
  undefined reference to `typecheck_pass_severity'
clang++: error: linker command failed with exit code 1
```

The preceding cycle's stage-2 log had already reported the same thing as a
non-fatal `warning: unresolved call typecheck_pass_severity in function ...`.
A warning at compile became a hard error at link.

## Cause

A single file, `src/compiler/80.driver/driver_hir_pipeline_lowering.spl`, was
copied from the `simple-main` checkout into the `simple-boot-snap` snapshot in
order to pick up one wanted change (the HIR in-flight build receipts of
`12cc5743eec`).

`main`'s copy of that file also carries, at line 43:

```
use compiler.driver.driver_typecheck_severity.{TypecheckPassSeverity, typecheck_pass_severity}
```

That import was added by an unrelated commit (`750e08c82c0`, routing the
declared-return-type check through `ctx`), and the module it names,
`src/compiler/80.driver/driver_typecheck_severity.spl`, **does not exist in the
snapshot at all**. Copying the file therefore imported a dangling dependency on
a whole change set nobody intended to sync.

## Why the pre-launch verification missed it

The sync was verified by checking that the symbols the *new code* CALLS resolve
in the target tree — `log_build_progress` was located and its arity confirmed at
10 parameters against 10 arguments. That check passed and was not sufficient.

The defect was not in what the new code called. It was in what the **whole file**
imported. A file-granular copy carries every `use` line in the file, including
ones belonging to commits outside the intended scope.

Note also that `cargo check`-style verification cannot catch this class: it skips
linking, so a declared-but-undefined symbol survives it. Only a real link does.

## Rule

When syncing a file between two trees at different commits:

1. Diff the file's **entire import block** against the target tree and confirm
   every imported module and symbol exists there. Not just the function being
   synced.
2. Prefer not copying the file at all. Restore the target tree's own version and
   apply only the wanted commits' hunks as patches.
3. After patching, assert that **no new `use` lines** were introduced:
   `git diff -- <path> | grep '^+use '` must be empty.
4. Verify by grepping the TARGET tree's copy, never the source tree's.

## Recommended technique (this is what fixed it)

```sh
# in the source repo: extract only the wanted hunks
git show 12cc5743eec -- src/compiler/80.driver/ > p1.patch
git show 454d1b1c3049 -- src/compiler/80.driver/ > p2.patch

# in the target tree: discard the bad copy, apply only those hunks
git checkout -- src/compiler/80.driver/driver_hir_pipeline_lowering.spl \
                src/compiler/80.driver/driver_source_pipeline_parsing.spl
git apply --check -v p1.patch && git apply p1.patch
git apply --check -v p2.patch && git apply p2.patch

# assert scope
git diff -- src/compiler/80.driver/ | grep '^+use '   # must print nothing
```

Applied to this instance, the receipts landed intact (15 surface-receipt sites,
6 HIR sites, 3 parse in-flight sites), `typecheck_pass_severity` count returned
to 0, and no new `use` lines appeared. The next cycle (4c) passed stage 2 and
reached stage 3.

## Related

- `doc/08_tracking/bug/stage3_post_parse_surface_window_has_no_receipts_2026-08-17.md`
- `doc/08_tracking/bug/native_build_class_surface_misses_newly_added_field_2026-08-17.md`
