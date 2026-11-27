# Absolute paths are mishandled in opposite directions by `native-build --entry` and `simple test` -- 2026-08-09
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## Status: RESOLVED (Half 1 implemented 2026-08-16; admitted Stage 2/4 verification pending. Half 2 resolved 2026-11-25 — see "Half 2 resolution (2026-11-25)" below: fail-closed classification and absolute-path handling verified on Windows, app-twin manifest-coverage gap fixed, regression coverage added.)

Two CLI entry points disagree about absolute paths, and they fail in *opposite*
ways. Anyone who hits one will eventually hit the other, so both halves are
recorded together.

## Half 1 -- `native-build` rejects an absolute `--entry` path (loud, wrong)

```
bin/simple native-build --entry /abs/path/to/entry.spl ...
  -> "native entry source not found"
```

The file exists and is readable. The **same file passed as a path relative to
the repo root works.** Observed today; it cost a fence iteration before the
absolute path was recognised as the variable.

Failure mode: LOUD and misleading. The message asserts the source does not
exist, but the retained Phase-2 evidence identified a narrower cause: the
single-file collector applied recursive/bulk exclusions to the full spelling.
`test/foo.spl` does not contain `/test/`, while
`/workspace/test/foo.spl` does, so only the absolute spelling was discarded.

**Workaround:** pass `--entry` as a path relative to the invocation root.

### 2026-08-16 containment

`_driver_collect_sources` now exempts only the direct `.spl` source whose
physical identity exactly matches `SIMPLE_NATIVE_BUILD_ENTRY`. Directory-walk
prefilters and unrelated explicit paths retain the existing exclusions. A
focused unit regression uses the retained failing fixture
`test/fixtures/compiler/type_multiline_signature_valid.spl`, proves its
absolute spelling remains filtered with both an empty and a nonmatching entry,
and proves only the exact requested absolute spelling is collected.

Latest retained failure evidence:

- compiler authority: admitted pure-Simple Phase 2,
  SHA-256 `530779a2240d35bfe7ce8834dfdb203b0f30651113a5708f91f853c3a94d654c`;
- rejected existing entry:
  `/mnt/data/worktrees/stage4-debug-frozen/test/fixtures/compiler/type_multiline_signature_valid.spl`;
- log:
  `build/native_probe/phase2-compiler-tools-matrix-20260816/compiler-smf-probe.log`.

This is implementation evidence only until a newly produced pure-Simple
compiler passes the focused native-build probe. Rust-seed/interpreter unit
evidence is diagnostic and cannot admit Stage 4.

Diagnostic verification on 2026-08-16:

- the exact admitted Stage-2 bootstrap capsule could not run the spec because
  that capsule intentionally exposes no `test` command (`unknown command`), so
  this was an infrastructure result and measured no criterion;
- installed pure-Simple CLI SHA-256
  `877dace60ce8eb11b656670b701019af5b4a0fb51b861832492bb5779237118b`
  ran the focused interpreter spec: 6 declared, 6 executed, 6 passed;
- evidence:
  `build/native_probe/phase2-absolute-entry-fix-20260816/focused-spec-bin-simple.log`.

## Half 2 -- `simple test <ABSOLUTE path>` runs nothing and exits 0 (silent, worse)

The known mirror-image trap. Given an absolute path, `simple test` runs no
specs, prints **no** `SPEC FILE VERDICT ... executed=N` line, and exits 0.
A caller that trusts the exit code reads this as GREEN.

**Workaround:** pass spec paths relative to the repo root, and never accept
`EXIT=0` from `simple test` as a pass -- require the verdict line with a
non-zero `executed=` count.

## Why the pair matters

The two halves are the same underlying gap -- no shared, tested policy for
absolute vs. relative path arguments across CLI subcommands -- but they fail
open and closed respectively:

| | absolute path | exit code | detectable? |
|---|---|---|---|
| `native-build --entry` | refuses to build | non-zero | yes, but blames a missing file |
| `simple test` | runs nothing | **0** | no -- looks like a pass |

The `simple test` half is the dangerous one: it manufactures false GREENs.

## Fix recipe

1. Normalise entry/spec path arguments once, in shared CLI argument handling:
   if the argument is already absolute, use it as-is; otherwise resolve it
   against the invocation root. Do not join unconditionally.
2. `native-build`: when the resolved entry does not exist, report the path that
   was actually probed, so the message cannot blame the user's path when the
   resolver rewrote it.
3. `simple test`: a spec-path argument that matches **zero** spec files must be
   a non-zero-exit ERROR, never a silent exit 0. A run that executed nothing is
   not a pass.

## Verification

- `native-build --entry` with an absolute path must produce the same artifact as
  the relative form (compare output binaries).
- `simple test <abs path>` must emit `SPEC FILE VERDICT ... executed=N` with the
  same `N` as the relative form; and `simple test <path matching nothing>` must
  exit non-zero.
- Both checks belong in the CLI-behaviour spec corpus so the asymmetry cannot
  silently return.


## Host-environment classification (2026-09-18)

Audited by the fix-pipeline classification review: **environment-blocked: windows** — [env-blocked:windows]. This row is not executable on the macOS aarch64 host fix lane; it resumes when the blocking condition clears.

## Half 2 resolution (2026-11-25, worktree wt-p2-abspath, branch work/p2-abspath-20261125)

Half 1 is unchanged by this pass; the 2026-08-16 containment above stands as-is.

### Root cause

Two independent mechanisms produced the silent exit-0:

1. **Prefix filter that only matched relative spellings.** The cached-manifest
   fast path in `discover_test_files_fast_with_manifest_path` filtered manifest
   entries with `path_is_within_directory(entry.path, base_path)`. Manifest
   entries are recorded in whatever spelling the indexing walk used (normally
   repo-relative), so an ABSOLUTE `base_path` could never prefix-match them and
   discovery returned zero files with no diagnostic.
2. **Empty selection classified as success.** A run that discovered zero files
   produced an empty `TestRunResult`, which the exit-code path treated as a
   pass, so the zero-match run exited 0 with no `SPEC FILE VERDICT` line.

### What was already fixed on release/1.0.0 before this pass

Verified on Windows with the tracked `bin/simple.exe`
(`SIMPLE_LIB=src bin/simple.exe test <path> --mode=interpreter`); the runner is
interpreted from worktree sources, so these are source-level facts:

- The fail-open half (mechanism 2) is closed at the classification layer:
  `test_empty_selection_is_success` (`src/lib/nogc_sync_mut/test_runner/test_runner_types.spl:206`)
  makes an explicit path that selects nothing an `EmptySelection`
  (`test_run_outcome_exit_code` = 4), never a pass. `--list`/`--spl-doctest`
  and non-explicit (default `test/`) runs keep their legitimate empty-is-ok
  semantics — the smallest compatible behavior for existing callers.
- The single-`.spl` client lane validates every requested path
  (`src/app/test_runner_new/test_runner_client.spl:150-155,829-830`) and exits 1
  naming the path.
- The std discovery twin
  (`src/lib/nogc_sync_mut/test_runner/test_runner_files.spl:485`) already gates
  the manifest fast path with `manifest_is_fresh(...) or not manifest_covers(...)`
  and falls back to walking, so absolute directory targets resolve correctly
  (mechanism 1, std lane).

### What this pass fixed

The app twin `src/app/test_runner_new/test_runner_files.spl`
(`discover_test_files_fast_with_manifest_path`, exercised via
`app.test_runner_new` exports and pinned for parity by
`test/02_integration/app/test_runner_cached_discovery_prefix_spec.spl`) still
trusted any fresh manifest regardless of which roots it had walked. An
absolute base path against a fresh relative-root manifest was prefix-filtered
to zero files silently (mechanism 1, app lane). The twin now mirrors the std
twin: `manifest_covers` gates the fast path, and a fallback scan that found
nothing is no longer cached over the previous index.

Regression coverage: a new scenario in
`test/02_integration/app/test_runner_cached_discovery_prefix_spec.spl`
("walks instead of trusting a fresh manifest that never indexed the absolute
spelling of the root") pins both twins: an absolute base path against a fresh
relative-root manifest must still discover the spec via the walk fallback.
Pre-fix (app-twin change stashed): `executed=3 passed=2 failed=1`, exit 1.
Post-fix: `executed=3 passed=3 failed=0`, exit 0.

### Before/after evidence (2026-11-25, Windows, bin/simple.exe)

The 2026-08-09 fail-open no longer reproduces at the CLI on this branch; the
commands below pin the current fail-closed behavior.

- `SIMPLE_LIB=src bin/simple.exe test D:/wt-p2-abspath/test/01_unit/app/argv_entry_script_suffix_heuristic_class_spec.spl --mode=interpreter`
  → exit 0,
  `SPEC FILE VERDICT: D:/wt-p2-abspath/.../argv_entry_script_suffix_heuristic_class_spec.spl outcome=OK declared>=6 executed=6 passed=6 failed=0 ...`
  (identical `executed=6` to the relative spelling; MSYS `/d/...` and
  backslash `D:\...` spellings behave the same).
- `SIMPLE_LIB=src bin/simple.exe test test/01_unit/app/no_such_thing_spec.spl --mode=interpreter`
  → exit 1, `ERROR: test file not found: test/01_unit/app/no_such_thing_spec.spl`
  (same for the absolute spelling of a missing file).
- `SIMPLE_LIB=src bin/simple.exe test test/00_unit --mode=interpreter`
  (existing directory that matches zero spec files)
  → exit 4, `No test files found in test/00_unit`.
- `SIMPLE_LIB=src bin/simple.exe test D:/wt-p2-abspath/test/01_unit/app/no_such_dir --mode=interpreter`
  → exit 4, `No test files found in D:/wt-p2-abspath/test/01_unit/app/no_such_dir`.
- App-twin discovery gap (pre-fix, change stashed):
  `SIMPLE_LIB=src bin/simple.exe test test/02_integration/app/test_runner_cached_discovery_prefix_spec.spl --mode=interpreter`
  → exit 1, `executed=3 passed=2 failed=1` (absolute base path discovered zero
  specs through the app twin). Post-fix: exit 0, `executed=3 passed=3 failed=0`.

Covering specs run once each, all green:
`test/01_unit/app/test_runner_new/discovery_path_boundary_spec.spl` (8/8),
`test/01_unit/app/tooling/test_runner_outcome_classification_spec.spl` (3/3),
`test/01_unit/app/test_runner_new/runner_files_filters_spec.spl` (65/65),
`test/02_integration/app/test_runner_cached_discovery_prefix_spec.spl` (3/3).

## Fleet verification note (2026-11-25, worktree wt-p2w1-ae, branch work/p2w1-ae-20261125)

Verified on `origin/release/1.0.0` HEAD (`38265c7f249`):

- PR #11547 ("fix(test-runner): gate app-twin cached discovery on manifest
  coverage (absolute-path Half 2)") is MERGED into `release/1.0.0`
  (mergedAt 2026-11-25T09:32:52Z, merge commit `866d31f9458`).
- Code inspection confirms the fix is present at HEAD:
  `src/app/test_runner_new/test_runner_files.spl:263` gates the app-twin
  cached-manifest fast path with `not manifest_is_fresh(manifest) or not
  manifest_covers(manifest, base_path)`, and the regression scenario
  "walks instead of trusting a fresh manifest that never indexed the absolute
  spelling of the root" is present in
  `test/02_integration/app/test_runner_cached_discovery_prefix_spec.spl:60`.
- Spec re-run is environment-blocked on this host: `SIMPLE_LIB=src
  bin/simple.exe test test/02_integration/app/test_runner_cached_discovery_prefix_spec.spl
  --mode=interpreter` fails repo-wide at HEAD with
  `unknown decorator '@representation_boundary'` (pinned Rust seed v1.0.0-rc.1
  predates commit `cfd89933699`'s decorator annotations). This is the known
  source/binary inconsistency, not a regression from this fix. The pre/post
  evidence recorded in the "Half 2 resolution (2026-11-25)" section above
  stands as the runnable verification.

Both halves RESOLVED: Half 1 by the 2026-08-16 containment (stands as-is),
Half 2 by PR #11547.
