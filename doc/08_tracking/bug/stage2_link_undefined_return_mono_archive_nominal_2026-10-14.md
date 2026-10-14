# Site 18: Stage 2 does not LINK on `release_phase3` — undefined `_return` from `MonomorphizationPass.ensure_archive_nominal_table_v2`

## Status: OPEN, found 2026-10-14 during the release_phase3 macOS bootstrap (goal lane: sync + bootstrap + land fixes)

## Symptom

Stage 1→2 bootstrap with the canonical candidate invocation:

```
sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --backend=llvm --mode=dynload --full-bootstrap \
  --stop-after-stage2 --no-mcp --jobs=4
```

fails at the Stage-2 native link on macOS aarch64 (isolated worktree at
`release_phase3` tip `fb78c0c652b`, macOS 26.5, Apple Clang 17 linker,
Homebrew LLVM 23 provider):

```
Undefined symbols for architecture arm64:
  "_return", referenced from:
      _compiler__mono__monomorphize_integration__MonomorphizationPass.ensure_archive_nominal_table_v2 in libspl_objects.a(mod_420.o)
ld: symbol(s) not found for architecture arm64
clang++: error: linker command failed with exit code 1
...
error: strict bootstrap stage2 failed (exit 1); refusing seed fallback
VERDICT — ABORTED: stage=stage2 exit=1 signal=none reason=stage2
```

Retained log:
`/private/tmp/simple-rp3-boot/.simple/storage/build/bootstrap/logs/aarch64-apple-darwin/stage2-native-build.log`
(transcript: `.../bootstrap/stage3/aarch64-apple-darwin/stage2-command.transcript`)

The compile itself completes; only the link fails. Same failure class as
`stage2_link_undefined_module_surfaces_promote_reason_sffi_enum_discriminant_2026-09-13.md`
(site 17): a dangling pure-Simple symbol reference, not a runtime extern gap.

## What the two names are

Neither name exists anywhere in `src/`, `test/`, or `doc/`:

- `grep -rn 'ensure_archive_nominal_table' src/` → 0 hits; the whole
  `src/compiler/40.mono/` tree contains no occurrence of `nominal` at all.
  `MonomorphizationPass` is defined only in
  `src/compiler/40.mono/monomorphize_integration.spl:40` and has no method
  whose name contains `ensure`, `archive`, or `nominal`.
- No function, method, field, or variable named `return` exists to back a
  `_return` symbol (`fn return` → 0 hits; `.return` field accesses only in
  comments/unrelated trees).

So the Stage-2 compiler (Rust seed compiling the Simple compiler sources)
fabricated a call pair — a callee symbol literally named `return` hanging off
a method reference `ensure_archive_nominal_table_v2` that has no source-level
definition. This is a name-resolution / symbol-emission defect in the seed's
handling of some construct inside the mono module, not a stale-snapshot
clobber like site 17's first symbol (no re-export/import of either name exists
to dangle).

## Relationship to open lanes

The 2026-10-13/14 phase-3 DRAFT PR batch targets exactly this "stage2 matrix
wall" family. Candidate overlaps to test before new work:

- PR #3479 `work/phase3-mono-index-guard-20261014`
  ("fix(compiler): lazy generic indexing and robustness warnings") touches
  `src/compiler/40.mono/monomorphize_integration.spl`
  (`build generic impl body index once on demand`) and
  `classify return operands explicitly`.
- PR #3462 `work/phase3-result-tuple-provider-astra-20261013`
  (fix(mir): preserve imported Result tuple collection owners).

Gate reminder (from `doc/03_plan/phase3_bootstrap_remaining_2026-10-13.md`):
Phase 3 and native Hello World must pass before landing compiler changes;
land fixes one at a time after review.

## Next steps

1. Reproduce after landing PR #3479 (or identify the fixing PR from the
   batch); do not blind-patch the mono module.
2. If still failing, bisect the seed's mono lowering: find which construct in
   `40.mono` (compiled into `mod_420.o`) emits a call to `_return`.
3. Keep this record's exact log paths in any fix PR body.
