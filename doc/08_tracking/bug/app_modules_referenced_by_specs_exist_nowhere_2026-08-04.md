# Three app modules/symbols their specs import exist nowhere in the tree

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
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

## Verification 2026-08-17 (wave_00 w0001/app_1) — CONFIRMED STILL OPEN

`/usr/bin/grep -rn 'handle_os_inline|handle_os_build_inline' src/` returns
ZERO definitions. The spec still names them:

- `test/01_unit/app/cli/cli_os_spec.spl:2` — `use app.cli.main.{handle_os_inline}`
- `test/01_unit/app/cli/cli_os_spec.spl:7,10,11,14,19,23,26,29` — 8 call sites

Shared root cause with
`doc/08_tracking/bug/dashboard_main_lost_table_model_2026-08-04.md`: a module
extraction/refactor left importers naming symbols the target module no longer
defines, and the compiler reports that only as `[use-warning]` while exiting 0.
Both rows are instances of the same fail-open `use`-resolution behaviour.
