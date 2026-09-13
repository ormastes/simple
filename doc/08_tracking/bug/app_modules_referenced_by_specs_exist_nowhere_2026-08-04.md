# Three app modules/symbols their specs import exist nowhere in the tree

## Re-triaged 2026-09-13 — 2 of 3 fixed, 1 repaired here, and a regression the spec was written to prevent has re-appeared

Binary: Rust seed `build/vt4/bootstrap/simple.exe` (sha256 `dc138d50276d…`),
Windows, `SIMPLE_BINARY=<abs> simple test`.

| spec | reported | measured 2026-09-13 |
|---|---|---|
| `test/01_unit/app/build/feature_flags_spec.spl` | 0 passed, 1 failed — `Cannot resolve module: app.build.feature_flags` | **17 total, 17 passed, 0 failed** |
| `test/01_unit/app/build/opt_remarks_spec.spl` | 0 passed, 1 failed — `Cannot resolve module: app.build.opt_remarks` | **13 total, 13 passed, 0 failed** |
| `test/01_unit/app/cli/cli_os_spec.spl` | 0 passed, 7 failed — `function handle_os_inline not found` (×7) | **7 total, 6 passed, 1 failed** after the repair below |
| `test/01_unit/app/cli/os_build_dispatch_spec.spl` | 0 passed, 1 failed | 1 total, 0 passed, 1 failed — **still red, and for a worse reason than filed** |

`src/app/build/feature_flags.spl` and `src/app/build/opt_remarks.spl` both exist
now; 30 examples run where 0 did. Those two rows are closed.

### `cli_os_spec` — repaired in this pass

`handle_os_inline` does not exist and never will: the symbol was **renamed**,
not lost. The live entry point is `fn handle_os(args: [text]) -> i64` at
`src/os/cli.spl:312` — *identical signature* — and it is genuinely wired into
the CLI (`src/app/cli/_CliMain/main_and_help.spl:50` imports it, `:624` does
`return handle_os(os_args)`). So this entry's claim that `simple os …` is "a
real CLI surface a user can invoke today and get nothing back" is **stale** for
the `os` case; the dispatch is present.

Repaired both copies of the spec (`test/01_unit/app/cli/` and the legacy
`test/unit/app/cli/`): `use app.cli.main.{handle_os_inline}` ->
`use os.cli.{handle_os}`, and the call sites likewise. Result **6 of 7 pass**
where 0 ran before. Note the legacy copy was a *half-done* migration — its
bodies already said `handle_os` while its import line still said
`handle_os_inline`, which is why it failed too. The two copies were divergent
and unbaselined (`unit:app/cli/cli_os_spec.spl` is absent from
`scripts/check/test_tree_divergence_baseline.txt`); they are now byte-identical,
which removes an unbaselined offender rather than creating one.

The single survivor is a real product defect newly exposed by making the spec
run: `dispatches os targets successfully` fails with
`semantic: class SimpleOsPlatformBuildTarget has no field named userland_target`.
Not investigated here.

### `os_build_dispatch_spec` — NOT stale. It is red because its invariant is now violated

This one is a source-text assertion over
`src/app/cli/_CliMain/args_and_os_commands.spl`. That file still exists, but
**none** of the three strings it asserts on are in it any more:
`fn handle_os_build_inline(args: [text]) -> i64:`,
`val target = get_target(arch_value)`, and the negative assertion's
`get_qemu_target(arch_value)` + `build_os(target)` pair. The OS build dispatch
moved to `src/os/cli.spl` (`fn handle_os_build` at `:160`).

The tempting conclusion is "stale spec, retarget or delete it". **Do not.** Read
what the third assertion is for: it requires that
`val target = get_qemu_target(...)` followed by `val ok = build_os(target)` be
**absent** — the spec exists to stop the OS build using QEMU targets instead of
kernel smoke targets. In the code that replaced it, `src/os/cli.spl:192-193`:

```
val target = get_qemu_target(arch.unwrap())
val ok = build_os(target)
```

**Exactly one site, and it is the one the spec guarded.** `:192-193` sits
inside `fn handle_os_build` (`:160`-`:201`). The same
`get_qemu_target` + `build_os` pair also appears at `:240-241` and `:297-298`,
but those are in `handle_os_run` and `handle_os_test` — the spec never guarded
the run or test paths, and using QEMU targets *there* may well be correct by
design. Do not count them.

Two checks on whether the build-path change was deliberate, both run
2026-09-13:

- `get_target` is **not** gone — it still exists as
  `fn get_target(arch: Architecture) -> OsTarget` at
  `src/os/_QemuRunner/runner_targets.spl:484`. So the spec's *positive*
  assertion still names a live function; this is not an invariant that was
  superseded because its subject disappeared.
- `git log -S 'handle_os_build_inline' -- src/app/cli` returns only large
  mechanical commits — a squashed 64-commit merge (`d9ce3993221`), a
  `fix(merge): repair 1136 unparseable .spl files from the share-history merge`
  (`e9da588ee61`), and a worktree-branch merge (`e274cd33719`). **None states an
  intentional change of build target policy.**

That is evidence of accidental decoupling during merge repair, not proof of it —
a deliberate change could still have been squashed into one of those commits
without a message. Stated as evidence, not verdict.

So this row stays OPEN, and it is not "a symbol that exists nowhere". It is **a
guard that lost contact with the code it guards**, and the one build-path site
it forbade is present again. Retargeting the spec at `src/os/cli.spl` must be
done *together with* an owner decision on whether `handle_os_build` should use
`get_qemu_target` or `get_target` — flipping the spec to match current code
would ratify the very thing it was written to forbid, and deleting it would
retire the question silently.

**Status:** OPEN
**Found:** 2026-08-04
**Severity:** high — 19 spec examples cannot run, and two of the three are real
CLI surfaces (`simple os …`, `simple build --target-feature …`) that a user can
invoke today and get nothing back

## Symptom

| Spec | Verdict | Runner error |
|---|---|---|
| `test/01_unit/app/build/feature_flags_spec.spl` | 0 passed, 1 failed | `semantic: Cannot resolve module: app.build.feature_flags` |
| `test/01_unit/app/build/opt_remarks_spec.spl` | 0 passed, 1 failed | `semantic: Cannot resolve module: app.build.opt_remarks` |
| `test/01_unit/app/cli/cli_os_spec.spl` | 0 passed, 7 failed | `semantic: function `handle_os_inline` not found` (×7) |
| `test/01_unit/app/cli/os_build_dispatch_spec.spl` | 0 passed, 1 failed | source-text assertion on `handle_os_build_inline` |

Repro for the first two:

```sh
SIMPLE_TIMEOUT_SECONDS=0 bin/simple test test/01_unit/app/build/feature_flags_spec.spl
```

Expected: the module resolves. Actual: `Cannot resolve module`.

## Root cause (each PROVED separately)

**1 & 2 — `app.build.feature_flags` / `app.build.opt_remarks` were never
committed.** `src/app/build/` holds exactly one file, `cli_entry.spl`.
`git log --all -- src/app/build/feature_flags.spl` lists commits, but
`git cat-file -s $(git rev-parse <c>:src/app/build/feature_flags.spl)` fails with
*"path does not exist"* on every one of them — the paths are only touched by
deletions, never added. The APIs the specs import
(`parse_target_features`, `apply_feature_overrides_x86/_aarch64/_rv64`,
`FeatureFlag`; `parse_opt_remarks`, `opt_remark_config_disabled`,
`emit_cipher_remark`, `emit_cipher_remark_if`, `OptRemarkConfig`) return **zero
hits** from `/usr/bin/grep -rn 'fn parse_target_features\|fn parse_opt_remarks\|fn
emit_cipher_remark' src/ --include=*.spl`. The specs' own `use
compiler.backend.feature_caps.{X86Caps, Aarch64Caps, Rv64Caps}` import *does*
resolve, so the specs were written against a real design that only ever landed
on the compiler side.

**3 — the SimpleOS CLI wrapper was dropped by the `_CliMain` split.**
`src/app/cli/main.spl` is now 17 lines that `export use
app.cli._CliMain.args_and_os_commands.*`, and that module (388 lines) contains
**no `handle_os_*` function at all** despite the name. The four handlers
(`handle_os_build_inline:271`, `handle_os_run_inline:314`,
`handle_os_test_inline:368`, `handle_os_inline:426`) last existed in
`src/app/cli/main_part1.spl` at `6a45d1b6efa` (2026-07-31), and
`git merge-base --is-ancestor 6a45d1b6efa HEAD` answers **NO**.

## Why not fixed now

For 1 & 2 this is new feature work, not a restore: there is no prior
implementation to recover, so writing `app.build.feature_flags` means designing
the x86/aarch64/rv64 override semantics from the spec's assertions alone, which
is exactly the kind of guess that produces a green test over a wrong
implementation.

For 3 the recoverable copy is **stale against its own spec**: `6a45d1b6efa`
writes `val target = get_qemu_target(arch.unwrap())`, while
`test/01_unit/app/cli/os_build_dispatch_spec.spl:11-12` asserts the source
contains `val target = get_target(arch_value)`. So the spec was written against a
*newer* revision than the one that survives, and a straight restore would still
leave `os_build_dispatch_spec` red while adding ~200 lines whose transitive
dependencies (`os_parse_log_arg`, `os_log_arg_error`, `os_parse_scenario_arg`,
`get_scenario`, `build_scenario`, `arch_from_name`, `get_qemu_target`,
`build_os`, `_export_os_log_mode_inline`, `_restore_os_log_mode_inline`) are
themselves absent and touch the SimpleOS/QEMU build path.
